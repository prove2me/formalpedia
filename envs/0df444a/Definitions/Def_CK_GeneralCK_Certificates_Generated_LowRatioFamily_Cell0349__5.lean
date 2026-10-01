-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0349__5
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0349__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T07:28:04.30206+00:00
-- url     : https://prove2.me/theorems/77c06a39-998f-4c98-aefd-36ad42e4319a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Cell0349 (+4 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Cell0350, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Cell0349 (+4 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Cell0350, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0351, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0352, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0353)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Cell0349 (+4 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Cell0350, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0351, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0352, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0353)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Cell0349 (+4 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Cell0350, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0351, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0352, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0353) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Cell0349 (+4 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Cell0350, GeneralCK/Certificates/Generated/LowRatioFamily/Cell0351, GeneralCK/Certificates/Generated/LowRatioFamily/Cell0352, GeneralCK/Certificates/Generated/LowRatioFamily/Cell0353).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0000__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0075__2

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Cell0349 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
theorem derivative_leaf_349 (a z s c : ℝ)
    (ha : Bounds (1849 / 10000) (37 / 200) a) (hz : Bounds 0 (1/1000) z)
    (hs : Bounds (1847151 / 20000000) (37037 / 400000) s) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (heq : biasE c = (((biasE a+biasE (a*z))/2)/s)*c) :
    ScFormula c a ((biasE a+biasE (a*z))/2)*(biasE c)^2 /
      (((biasE a+biasE (a*z))/2)*biasB c) < (3653882551473364697152287469 / 9327928000277601000000000000) := by
  let x0 : ℝ := Real.log (2 / 1)
  have hx0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x0 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x1 : ℝ := (1 / 1)+(37 / 200)
  have hx1 : Bounds (237 / 200) (237 / 200) x1 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((37 / 200) : ℝ)) <;> norm_num
  let x2 : ℝ := (1 / 1)+(37 / 200)
  have hx2 : Bounds (237 / 200) (237 / 200) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((37 / 200) : ℝ)) <;> norm_num
  let x3 : ℝ := Real.log x2
  have hx3 : Bounds (84871387 / 500000000) (6789711 / 40000000) x3 := by
    exact bounds_log hx2 (by norm_num) (by simpa only [div_one] using reflection_log_4856.1) (by simpa only [div_one] using reflection_log_4856.2)
  let x4 : ℝ := x1*x3
  have hx4 : Bounds (20114518719 / 100000000000) (1609161507 / 8000000000) x4 := by
    apply bounds_mul hx1 hx3 <;> norm_num
  let x5 : ℝ := -(37 / 200)
  have hx5 : Bounds (-37 / 200) (-37 / 200) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((37 / 200) : ℝ))
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (163 / 200) (163 / 200) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-(37 / 200)
  have hx7 : Bounds (163 / 200) (163 / 200) x7 := by
    exact hx6
  let x8 : ℝ := -(37 / 200)
  have hx8 : Bounds (-37 / 200) (-37 / 200) x8 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((37 / 200) : ℝ))
  let x9 : ℝ := (1 / 1)+x8
  have hx9 : Bounds (163 / 200) (163 / 200) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx8 <;> norm_num
  let x10 : ℝ := (1 / 1)-(37 / 200)
  have hx10 : Bounds (163 / 200) (163 / 200) x10 := by
    exact hx9
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (-102283583 / 500000000) (-40913433 / 200000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_4857.1) (by simpa only [div_one] using reflection_log_4857.2)
  let x12 : ℝ := x7*x11
  have hx12 : Bounds (-16672224029 / 100000000000) (-6668889579 / 40000000000) x12 := by
    apply bounds_mul hx7 hx11 <;> norm_num
  let x13 : ℝ := x4+x12
  have hx13 : Bounds (344229469 / 10000000000) (344229489 / 10000000000) x13 := by
    apply bounds_add hx4 hx12 <;> norm_num
  let x14 : ℝ := (2 / 1)⁻¹
  have hx14 : Bounds (1 / 2) (1 / 2) x14 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x15 : ℝ := x13*x14
  have hx15 : Bounds (344229469 / 20000000000) (344229489 / 20000000000) x15 := by
    apply bounds_mul hx13 hx14 <;> norm_num
  let x16 : ℝ := x13/(2 / 1)
  have hx16 : Bounds (344229469 / 20000000000) (344229489 / 20000000000) x16 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx15
  let x17 : ℝ := -x16
  have hx17 : Bounds (-344229489 / 20000000000) (-344229469 / 20000000000) x17 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx16
  let x18 : ℝ := x0+x17
  have hx18 : Bounds (13518714111 / 20000000000) (13518714151 / 20000000000) x18 := by
    apply bounds_add hx0 hx17 <;> norm_num
  let x19 : ℝ := x0-x16
  have hx19 : Bounds (13518714111 / 20000000000) (13518714151 / 20000000000) x19 := by
    exact hx18
  let x20 : ℝ := biasE (37 / 200)
  have hx20 : Bounds (13518714111 / 20000000000) (13518714151 / 20000000000) x20 := by
    simpa +zetaDelta only [biasE, div_one] using hx19
  let x21 : ℝ := Real.log (2 / 1)
  have hx21 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x21 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x22 : ℝ := (1 / 1)+(1849 / 10000)
  have hx22 : Bounds (11849 / 10000) (11849 / 10000) x22 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1849 / 10000) : ℝ)) <;> norm_num
  let x23 : ℝ := (1 / 1)+(1849 / 10000)
  have hx23 : Bounds (11849 / 10000) (11849 / 10000) x23 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1849 / 10000) : ℝ)) <;> norm_num
  let x24 : ℝ := Real.log x23
  have hx24 : Bounds (84829191 / 500000000) (169658383 / 1000000000) x24 := by
    exact bounds_log hx23 (by norm_num) (by simpa only [div_one] using reflection_log_4842.1) (by simpa only [div_one] using reflection_log_4842.2)
  let x25 : ℝ := x22*x24
  have hx25 : Bounds (201028216831 / 1000000000000) (201028218017 / 1000000000000) x25 := by
    apply bounds_mul hx22 hx24 <;> norm_num
  let x26 : ℝ := -(1849 / 10000)
  have hx26 : Bounds (-1849 / 10000) (-1849 / 10000) x26 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1849 / 10000) : ℝ))
  let x27 : ℝ := (1 / 1)+x26
  have hx27 : Bounds (8151 / 10000) (8151 / 10000) x27 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx26 <;> norm_num
  let x28 : ℝ := (1 / 1)-(1849 / 10000)
  have hx28 : Bounds (8151 / 10000) (8151 / 10000) x28 := by
    exact hx27
  let x29 : ℝ := -(1849 / 10000)
  have hx29 : Bounds (-1849 / 10000) (-1849 / 10000) x29 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1849 / 10000) : ℝ))
  let x30 : ℝ := (1 / 1)+x29
  have hx30 : Bounds (8151 / 10000) (8151 / 10000) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx29 <;> norm_num
  let x31 : ℝ := (1 / 1)-(1849 / 10000)
  have hx31 : Bounds (8151 / 10000) (8151 / 10000) x31 := by
    exact hx30
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (-102222237 / 500000000) (-204444473 / 1000000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_4843.1) (by simpa only [div_one] using reflection_log_4843.2)
  let x33 : ℝ := x28*x32
  have hx33 : Bounds (-83321345379 / 500000000000) (-83321344971 / 500000000000) x33 := by
    apply bounds_mul hx28 hx32 <;> norm_num
  let x34 : ℝ := x25+x33
  have hx34 : Bounds (34385526073 / 1000000000000) (1375421123 / 40000000000) x34 := by
    apply bounds_add hx25 hx33 <;> norm_num
  let x35 : ℝ := (2 / 1)⁻¹
  have hx35 : Bounds (1 / 2) (1 / 2) x35 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x36 : ℝ := x34*x35
  have hx36 : Bounds (4298190759 / 250000000000) (8596382019 / 500000000000) x36 := by
    apply bounds_mul hx34 hx35 <;> norm_num
  let x37 : ℝ := x34/(2 / 1)
  have hx37 : Bounds (4298190759 / 250000000000) (8596382019 / 500000000000) x37 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx36
  let x38 : ℝ := -x37
  have hx38 : Bounds (-8596382019 / 500000000000) (-4298190759 / 250000000000) x38 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx37
  let x39 : ℝ := x21+x38
  have hx39 : Bounds (337977207981 / 500000000000) (168988604491 / 250000000000) x39 := by
    apply bounds_add hx21 hx38 <;> norm_num
  let x40 : ℝ := x21-x37
  have hx40 : Bounds (337977207981 / 500000000000) (168988604491 / 250000000000) x40 := by
    exact hx39
  let x41 : ℝ := biasE (1849 / 10000)
  have hx41 : Bounds (337977207981 / 500000000000) (168988604491 / 250000000000) x41 := by
    simpa +zetaDelta only [biasE, div_one] using hx40
  let x42 : ℝ := biasE a
  have hx42 : Bounds (13518714111 / 20000000000) (168988604491 / 250000000000) x42 := by
    exact bounds_biasE ha (by norm_num) (by norm_num) hx20.1 hx41.2
  let x43 : ℝ := a*z
  have hx43 : Bounds (0 / 1) (37 / 200000) x43 := by
    apply bounds_mul ha hz <;> norm_num
  let x44 : ℝ := Real.log (2 / 1)
  have hx44 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x44 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x45 : ℝ := (1 / 1)+(37 / 200000)
  have hx45 : Bounds (200037 / 200000) (200037 / 200000) x45 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((37 / 200000) : ℝ)) <;> norm_num
  let x46 : ℝ := (1 / 1)+(37 / 200000)
  have hx46 : Bounds (200037 / 200000) (200037 / 200000) x46 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((37 / 200000) : ℝ)) <;> norm_num
  let x47 : ℝ := Real.log x46
  have hx47 : Bounds (92491 / 500000000) (184983 / 1000000000) x47 := by
    exact bounds_log hx46 (by norm_num) (by simpa only [div_one] using reflection_log_4858.1) (by simpa only [div_one] using reflection_log_4858.2)
  let x48 : ℝ := x45*x47
  have hx48 : Bounds (185016221 / 1000000000000) (92508611 / 500000000000) x48 := by
    apply bounds_mul hx45 hx47 <;> norm_num
  let x49 : ℝ := -(37 / 200000)
  have hx49 : Bounds (-37 / 200000) (-37 / 200000) x49 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((37 / 200000) : ℝ))
  let x50 : ℝ := (1 / 1)+x49
  have hx50 : Bounds (199963 / 200000) (199963 / 200000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx49 <;> norm_num
  let x51 : ℝ := (1 / 1)-(37 / 200000)
  have hx51 : Bounds (199963 / 200000) (199963 / 200000) x51 := by
    exact hx50
  let x52 : ℝ := -(37 / 200000)
  have hx52 : Bounds (-37 / 200000) (-37 / 200000) x52 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((37 / 200000) : ℝ))
  let x53 : ℝ := (1 / 1)+x52
  have hx53 : Bounds (199963 / 200000) (199963 / 200000) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx52 <;> norm_num
  let x54 : ℝ := (1 / 1)-(37 / 200000)
  have hx54 : Bounds (199963 / 200000) (199963 / 200000) x54 := by
    exact hx53
  let x55 : ℝ := Real.log x54
  have hx55 : Bounds (-92509 / 500000000) (-185017 / 1000000000) x55 := by
    exact bounds_log hx54 (by norm_num) (by simpa only [div_one] using reflection_log_4859.1) (by simpa only [div_one] using reflection_log_4859.2)
  let x56 : ℝ := x51*x55
  have hx56 : Bounds (-46245943 / 250000000000) (-184982771 / 1000000000000) x56 := by
    apply bounds_mul hx51 hx55 <;> norm_num
  let x57 : ℝ := x48+x56
  have hx57 : Bounds (32449 / 1000000000000) (34451 / 1000000000000) x57 := by
    apply bounds_add hx48 hx56 <;> norm_num
  let x58 : ℝ := (2 / 1)⁻¹
  have hx58 : Bounds (1 / 2) (1 / 2) x58 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x59 : ℝ := x57*x58
  have hx59 : Bounds (507 / 31250000000) (8613 / 500000000000) x59 := by
    apply bounds_mul hx57 hx58 <;> norm_num
  let x60 : ℝ := x57/(2 / 1)
  have hx60 : Bounds (507 / 31250000000) (8613 / 500000000000) x60 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx59
  let x61 : ℝ := -x60
  have hx61 : Bounds (-8613 / 500000000000) (-507 / 31250000000) x61 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx60
  let x62 : ℝ := x44+x61
  have hx62 : Bounds (346573581387 / 500000000000) (86643395597 / 125000000000) x62 := by
    apply bounds_add hx44 hx61 <;> norm_num
  let x63 : ℝ := x44-x60
  have hx63 : Bounds (346573581387 / 500000000000) (86643395597 / 125000000000) x63 := by
    exact hx62
  let x64 : ℝ := biasE (37 / 200000)
  have hx64 : Bounds (346573581387 / 500000000000) (86643395597 / 125000000000) x64 := by
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
  have hx86 : Bounds (346573581387 / 500000000000) (693147181 / 1000000000) x86 := by
    exact bounds_biasE hx43 (by norm_num) (by norm_num) hx64.1 hx85.2
  let x87 : ℝ := x42+x86
  have hx87 : Bounds (342270717081 / 250000000000) (342275399741 / 250000000000) x87 := by
    apply bounds_add hx42 hx86 <;> norm_num
  let x88 : ℝ := (2 / 1)⁻¹
  have hx88 : Bounds (1 / 2) (1 / 2) x88 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x89 : ℝ := x87*x88
  have hx89 : Bounds (342270717081 / 500000000000) (342275399741 / 500000000000) x89 := by
    apply bounds_mul hx87 hx88 <;> norm_num
  let x90 : ℝ := x87/(2 / 1)
  have hx90 : Bounds (342270717081 / 500000000000) (342275399741 / 500000000000) x90 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx89
  let x91 : ℝ := s⁻¹
  have hx91 : Bounds (1080001080001 / 100000000000) (2706871284481 / 250000000000) x91 := by
    apply bounds_inv hs <;> norm_num
  let x92 : ℝ := x90*x91
  have hx92 : Bounds (7393054882003 / 1000000000000) (3705981803773 / 500000000000) x92 := by
    apply bounds_mul hx90 hx91 <;> norm_num
  let x93 : ℝ := x90/s
  have hx93 : Bounds (7393054882003 / 1000000000000) (3705981803773 / 500000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(92933 / 1000000)
  have hx95 : Bounds (1092933 / 1000000) (1092933 / 1000000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((92933 / 1000000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(92933 / 1000000)
  have hx96 : Bounds (1092933 / 1000000) (1092933 / 1000000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((92933 / 1000000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (22216227 / 250000000) (88864909 / 1000000000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_4860.1) (by simpa only [div_one] using reflection_log_4860.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (19424678099 / 200000000000) (97123391589 / 1000000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(92933 / 1000000)
  have hx99 : Bounds (-92933 / 1000000) (-92933 / 1000000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((92933 / 1000000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (907067 / 1000000) (907067 / 1000000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(92933 / 1000000)
  have hx101 : Bounds (907067 / 1000000) (907067 / 1000000) x101 := by
    exact hx100
  let x102 : ℝ := -(92933 / 1000000)
  have hx102 : Bounds (-92933 / 1000000) (-92933 / 1000000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((92933 / 1000000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (907067 / 1000000) (907067 / 1000000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(92933 / 1000000)
  have hx104 : Bounds (907067 / 1000000) (907067 / 1000000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-48769481 / 500000000) (-97538961 / 1000000000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_4861.1) (by simpa only [div_one] using reflection_log_4861.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-17694874729 / 200000000000) (-88474372737 / 1000000000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (172980337 / 20000000000) (2162254713 / 250000000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (172980337 / 40000000000) (2162254713 / 500000000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (172980337 / 40000000000) (2162254713 / 500000000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-2162254713 / 500000000000) (-172980337 / 40000000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (344411335287 / 500000000000) (27552906903 / 40000000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (344411335287 / 500000000000) (27552906903 / 40000000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (92933 / 1000000)
  have hx114 : Bounds (344411335287 / 500000000000) (27552906903 / 40000000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(93169 / 1000000)
  have hx116 : Bounds (1093169 / 1000000) (1093169 / 1000000) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((93169 / 1000000) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(93169 / 1000000)
  have hx117 : Bounds (1093169 / 1000000) (1093169 / 1000000) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((93169 / 1000000) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (89080817 / 1000000000) (44540409 / 500000000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_4862.1) (by simpa only [div_one] using reflection_log_4862.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (97380387639 / 1000000000000) (97380388733 / 1000000000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(93169 / 1000000)
  have hx120 : Bounds (-93169 / 1000000) (-93169 / 1000000) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((93169 / 1000000) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (906831 / 1000000) (906831 / 1000000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(93169 / 1000000)
  have hx122 : Bounds (906831 / 1000000) (906831 / 1000000) x122 := by
    exact hx121
  let x123 : ℝ := -(93169 / 1000000)
  have hx123 : Bounds (-93169 / 1000000) (-93169 / 1000000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((93169 / 1000000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (906831 / 1000000) (906831 / 1000000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(93169 / 1000000)
  have hx125 : Bounds (906831 / 1000000) (906831 / 1000000) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-3911967 / 40000000) (-48899587 / 500000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_4863.1) (by simpa only [div_one] using reflection_log_4863.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-17737464733 / 200000000000) (-88687322757 / 1000000000000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (4346531987 / 500000000000) (1086633247 / 125000000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (4346531987 / 1000000000000) (1086633247 / 250000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (4346531987 / 1000000000000) (1086633247 / 250000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-1086633247 / 250000000000) (-4346531987 / 1000000000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (172200161753 / 250000000000) (688800649013 / 1000000000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (172200161753 / 250000000000) (688800649013 / 1000000000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (93169 / 1000000)
  have hx135 : Bounds (172200161753 / 250000000000) (688800649013 / 1000000000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(92933 / 1000000)
  have hx136 : Bounds (687058769349 / 1000000000000) (688816013941 / 1000000000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((92933 / 1000000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(93169 / 1000000)
  have hx137 : Bounds (688803530301 / 1000000000000) (86320654669 / 125000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((93169 / 1000000) : ℝ)) <;> norm_num
  have hc : Bounds (92933 / 1000000) (93169 / 1000000) c := by
    apply contact_bracket hc0 hc1 (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x93 by linarith [hx93.1])
      (show biasE c = x93*c by simpa +zetaDelta only [div_one] using heq)
    · have h1 : x93*(92933 / 1000000) ≤ (688816013941 / 1000000000000) := hx136.2
      have h2 : (344411335287 / 500000000000) ≤ biasE (92933 / 1000000) := hx114.1
      linarith
    · have h1 : biasE (93169 / 1000000) ≤ (688800649013 / 1000000000000) := hx135.2
      have h2 : (688803530301 / 1000000000000) ≤ x93*(93169 / 1000000) := hx137.1
      linarith
  let x138 : ℝ := Real.log (2 / 1)
  have hx138 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x138 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x139 : ℝ := (1 / 1)+(93169 / 1000000)
  have hx139 : Bounds (1093169 / 1000000) (1093169 / 1000000) x139 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((93169 / 1000000) : ℝ)) <;> norm_num
  let x140 : ℝ := (1 / 1)+(93169 / 1000000)
  have hx140 : Bounds (1093169 / 1000000) (1093169 / 1000000) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((93169 / 1000000) : ℝ)) <;> norm_num
  let x141 : ℝ := Real.log x140
  have hx141 : Bounds (89080817 / 1000000000) (44540409 / 500000000) x141 := by
    exact bounds_log hx140 (by norm_num) (by simpa only [div_one] using reflection_log_4862.1) (by simpa only [div_one] using reflection_log_4862.2)
  let x142 : ℝ := x139*x141
  have hx142 : Bounds (97380387639 / 1000000000000) (97380388733 / 1000000000000) x142 := by
    apply bounds_mul hx139 hx141 <;> norm_num
  let x143 : ℝ := -(93169 / 1000000)
  have hx143 : Bounds (-93169 / 1000000) (-93169 / 1000000) x143 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((93169 / 1000000) : ℝ))
  let x144 : ℝ := (1 / 1)+x143
  have hx144 : Bounds (906831 / 1000000) (906831 / 1000000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx143 <;> norm_num
  let x145 : ℝ := (1 / 1)-(93169 / 1000000)
  have hx145 : Bounds (906831 / 1000000) (906831 / 1000000) x145 := by
    exact hx144
  let x146 : ℝ := -(93169 / 1000000)
  have hx146 : Bounds (-93169 / 1000000) (-93169 / 1000000) x146 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((93169 / 1000000) : ℝ))
  let x147 : ℝ := (1 / 1)+x146
  have hx147 : Bounds (906831 / 1000000) (906831 / 1000000) x147 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx146 <;> norm_num
  let x148 : ℝ := (1 / 1)-(93169 / 1000000)
  have hx148 : Bounds (906831 / 1000000) (906831 / 1000000) x148 := by
    exact hx147
  let x149 : ℝ := Real.log x148
  have hx149 : Bounds (-3911967 / 40000000) (-48899587 / 500000000) x149 := by
    exact bounds_log hx148 (by norm_num) (by simpa only [div_one] using reflection_log_4863.1) (by simpa only [div_one] using reflection_log_4863.2)
  let x150 : ℝ := x145*x149
  have hx150 : Bounds (-17737464733 / 200000000000) (-88687322757 / 1000000000000) x150 := by
    apply bounds_mul hx145 hx149 <;> norm_num
  let x151 : ℝ := x142+x150
  have hx151 : Bounds (4346531987 / 500000000000) (1086633247 / 125000000000) x151 := by
    apply bounds_add hx142 hx150 <;> norm_num
  let x152 : ℝ := (2 / 1)⁻¹
  have hx152 : Bounds (1 / 2) (1 / 2) x152 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x153 : ℝ := x151*x152
  have hx153 : Bounds (4346531987 / 1000000000000) (1086633247 / 250000000000) x153 := by
    apply bounds_mul hx151 hx152 <;> norm_num
  let x154 : ℝ := x151/(2 / 1)
  have hx154 : Bounds (4346531987 / 1000000000000) (1086633247 / 250000000000) x154 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx153
  let x155 : ℝ := -x154
  have hx155 : Bounds (-1086633247 / 250000000000) (-4346531987 / 1000000000000) x155 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx154
  let x156 : ℝ := x138+x155
  have hx156 : Bounds (172200161753 / 250000000000) (688800649013 / 1000000000000) x156 := by
    apply bounds_add hx138 hx155 <;> norm_num
  let x157 : ℝ := x138-x154
  have hx157 : Bounds (172200161753 / 250000000000) (688800649013 / 1000000000000) x157 := by
    exact hx156
  let x158 : ℝ := biasE (93169 / 1000000)
  have hx158 : Bounds (172200161753 / 250000000000) (688800649013 / 1000000000000) x158 := by
    simpa +zetaDelta only [biasE, div_one] using hx157
  let x159 : ℝ := Real.log (2 / 1)
  have hx159 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x159 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x160 : ℝ := (1 / 1)+(92933 / 1000000)
  have hx160 : Bounds (1092933 / 1000000) (1092933 / 1000000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((92933 / 1000000) : ℝ)) <;> norm_num
  let x161 : ℝ := (1 / 1)+(92933 / 1000000)
  have hx161 : Bounds (1092933 / 1000000) (1092933 / 1000000) x161 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((92933 / 1000000) : ℝ)) <;> norm_num
  let x162 : ℝ := Real.log x161
  have hx162 : Bounds (22216227 / 250000000) (88864909 / 1000000000) x162 := by
    exact bounds_log hx161 (by norm_num) (by simpa only [div_one] using reflection_log_4860.1) (by simpa only [div_one] using reflection_log_4860.2)
  let x163 : ℝ := x160*x162
  have hx163 : Bounds (19424678099 / 200000000000) (97123391589 / 1000000000000) x163 := by
    apply bounds_mul hx160 hx162 <;> norm_num
  let x164 : ℝ := -(92933 / 1000000)
  have hx164 : Bounds (-92933 / 1000000) (-92933 / 1000000) x164 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((92933 / 1000000) : ℝ))
  let x165 : ℝ := (1 / 1)+x164
  have hx165 : Bounds (907067 / 1000000) (907067 / 1000000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx164 <;> norm_num
  let x166 : ℝ := (1 / 1)-(92933 / 1000000)
  have hx166 : Bounds (907067 / 1000000) (907067 / 1000000) x166 := by
    exact hx165
  let x167 : ℝ := -(92933 / 1000000)
  have hx167 : Bounds (-92933 / 1000000) (-92933 / 1000000) x167 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((92933 / 1000000) : ℝ))
  let x168 : ℝ := (1 / 1)+x167
  have hx168 : Bounds (907067 / 1000000) (907067 / 1000000) x168 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx167 <;> norm_num
  let x169 : ℝ := (1 / 1)-(92933 / 1000000)
  have hx169 : Bounds (907067 / 1000000) (907067 / 1000000) x169 := by
    exact hx168
  let x170 : ℝ := Real.log x169
  have hx170 : Bounds (-48769481 / 500000000) (-97538961 / 1000000000) x170 := by
    exact bounds_log hx169 (by norm_num) (by simpa only [div_one] using reflection_log_4861.1) (by simpa only [div_one] using reflection_log_4861.2)
  let x171 : ℝ := x166*x170
  have hx171 : Bounds (-17694874729 / 200000000000) (-88474372737 / 1000000000000) x171 := by
    apply bounds_mul hx166 hx170 <;> norm_num
  let x172 : ℝ := x163+x171
  have hx172 : Bounds (172980337 / 20000000000) (2162254713 / 250000000000) x172 := by
    apply bounds_add hx163 hx171 <;> norm_num
  let x173 : ℝ := (2 / 1)⁻¹
  have hx173 : Bounds (1 / 2) (1 / 2) x173 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x174 : ℝ := x172*x173
  have hx174 : Bounds (172980337 / 40000000000) (2162254713 / 500000000000) x174 := by
    apply bounds_mul hx172 hx173 <;> norm_num
  let x175 : ℝ := x172/(2 / 1)
  have hx175 : Bounds (172980337 / 40000000000) (2162254713 / 500000000000) x175 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx174
  let x176 : ℝ := -x175
  have hx176 : Bounds (-2162254713 / 500000000000) (-172980337 / 40000000000) x176 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx175
  let x177 : ℝ := x159+x176
  have hx177 : Bounds (344411335287 / 500000000000) (27552906903 / 40000000000) x177 := by
    apply bounds_add hx159 hx176 <;> norm_num
  let x178 : ℝ := x159-x175
  have hx178 : Bounds (344411335287 / 500000000000) (27552906903 / 40000000000) x178 := by
    exact hx177
  let x179 : ℝ := biasE (92933 / 1000000)
  have hx179 : Bounds (344411335287 / 500000000000) (27552906903 / 40000000000) x179 := by
    simpa +zetaDelta only [biasE, div_one] using hx178
  let x180 : ℝ := biasE c
  have hx180 : Bounds (172200161753 / 250000000000) (27552906903 / 40000000000) x180 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx158.1 hx179.2
  let x181 : ℝ := Real.log (2 / 1)
  have hx181 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x181 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x182 : ℝ := c*c
  have hx182 : Bounds (8636542489 / 1000000000000) (8680462561 / 1000000000000) x182 := by
    apply bounds_mul hc hc <;> norm_num
  let x183 : ℝ := -x182
  have hx183 : Bounds (-8680462561 / 1000000000000) (-8636542489 / 1000000000000) x183 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx182
  let x184 : ℝ := (1 / 1)+x183
  have hx184 : Bounds (991319537439 / 1000000000000) (991363457511 / 1000000000000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx183 <;> norm_num
  let x185 : ℝ := (1 / 1)-x182
  have hx185 : Bounds (991319537439 / 1000000000000) (991363457511 / 1000000000000) x185 := by
    exact hx184
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (-4359179 / 500000000) (-8674053 / 1000000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_4864.1) (by simpa only [div_one] using reflection_log_4865.2)
  let x187 : ℝ := (2 / 1)⁻¹
  have hx187 : Bounds (1 / 2) (1 / 2) x187 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x188 : ℝ := x186*x187
  have hx188 : Bounds (-4359179 / 1000000000) (-8674053 / 2000000000) x188 := by
    apply bounds_mul hx186 hx187 <;> norm_num
  let x189 : ℝ := x186/(2 / 1)
  have hx189 : Bounds (-4359179 / 1000000000) (-8674053 / 2000000000) x189 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx188
  let x190 : ℝ := -x189
  have hx190 : Bounds (8674053 / 2000000000) (4359179 / 1000000000) x190 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx189
  let x191 : ℝ := x181+x190
  have hx191 : Bounds (1394968413 / 2000000000) (17437659 / 25000000) x191 := by
    apply bounds_add hx181 hx190 <;> norm_num
  let x192 : ℝ := x181-x189
  have hx192 : Bounds (1394968413 / 2000000000) (17437659 / 25000000) x192 := by
    exact hx191
  let x193 : ℝ := c*(1 / 1)
  have hx193 : Bounds (92933 / 1000000) (93169 / 1000000) x193 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x194 : ℝ := c*x193
  have hx194 : Bounds (8636542489 / 1000000000000) (8680462561 / 1000000000000) x194 := by
    apply bounds_mul hc hx193 <;> norm_num
  let x195 : ℝ := c^2
  have hx195 : Bounds (8636542489 / 1000000000000) (8680462561 / 1000000000000) x195 := by
    (convert hx194 using 1; ring)
  let x196 : ℝ := -x195
  have hx196 : Bounds (-8680462561 / 1000000000000) (-8636542489 / 1000000000000) x196 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx195
  let x197 : ℝ := (1 / 1)+x196
  have hx197 : Bounds (991319537439 / 1000000000000) (991363457511 / 1000000000000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx196 <;> norm_num
  let x198 : ℝ := (1 / 1)-x195
  have hx198 : Bounds (991319537439 / 1000000000000) (991363457511 / 1000000000000) x198 := by
    exact hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (1092933 / 1000000) (1093169 / 1000000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-93169 / 1000000) (-92933 / 1000000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (906831 / 1000000) (907067 / 1000000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (906831 / 1000000) (907067 / 1000000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (1102454394217 / 1000000000000) (110274130461 / 100000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (602454394217 / 500000000000) (60274130461 / 50000000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (602454394217 / 500000000000) (60274130461 / 50000000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (186403869 / 1000000000) (186879993 / 1000000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_4866.1) (by simpa only [div_one] using reflection_log_4867.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (186403869 / 2000000000) (186879993 / 2000000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (186403869 / 2000000000) (186879993 / 2000000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (1 / 1)+a
  have hx210 : Bounds (11849 / 10000) (237 / 200) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) ha <;> norm_num
  let x211 : ℝ := -a
  have hx211 : Bounds (-37 / 200) (-1849 / 10000) x211 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg ha
  let x212 : ℝ := (1 / 1)+x211
  have hx212 : Bounds (163 / 200) (8151 / 10000) x212 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx211 <;> norm_num
  let x213 : ℝ := (1 / 1)-a
  have hx213 : Bounds (163 / 200) (8151 / 10000) x213 := by
    exact hx212
  let x214 : ℝ := x213⁻¹
  have hx214 : Bounds (613421666053 / 500000000000) (1226993865031 / 1000000000000) x214 := by
    apply bounds_inv hx213 <;> norm_num
  let x215 : ℝ := x210*x214
  have hx215 : Bounds (363421666053 / 250000000000) (726993865031 / 500000000000) x215 := by
    apply bounds_mul hx210 hx214 <;> norm_num
  let x216 : ℝ := x210/x213
  have hx216 : Bounds (363421666053 / 250000000000) (726993865031 / 500000000000) x216 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx215
  let x217 : ℝ := Real.log x216
  have hx217 : Bounds (46762857 / 125000000) (374309941 / 1000000000) x217 := by
    exact bounds_log hx216 (by norm_num) (by simpa only [div_one] using reflection_log_4868.1) (by simpa only [div_one] using reflection_log_4869.2)
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (46762857 / 250000000) (374309941 / 2000000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (46762857 / 250000000) (374309941 / 2000000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := (2 / 1)*x192
  have hx221 : Bounds (1394968413 / 1000000000) (17437659 / 12500000) x221 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x222 : ℝ := c*(1 / 1)
  have hx222 : Bounds (92933 / 1000000) (93169 / 1000000) x222 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x223 : ℝ := c*x222
  have hx223 : Bounds (8636542489 / 1000000000000) (8680462561 / 1000000000000) x223 := by
    apply bounds_mul hc hx222 <;> norm_num
  let x224 : ℝ := c^2
  have hx224 : Bounds (8636542489 / 1000000000000) (8680462561 / 1000000000000) x224 := by
    (convert hx223 using 1; ring)
  let x225 : ℝ := -x224
  have hx225 : Bounds (-8680462561 / 1000000000000) (-8636542489 / 1000000000000) x225 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx224
  let x226 : ℝ := x221+x225
  have hx226 : Bounds (1386287950439 / 1000000000000) (1386376177511 / 1000000000000) x226 := by
    apply bounds_add hx221 hx225 <;> norm_num
  let x227 : ℝ := x221-x224
  have hx227 : Bounds (1386287950439 / 1000000000000) (1386376177511 / 1000000000000) x227 := by
    exact hx226
  let x228 : ℝ := x180*x227
  have hx228 : Bounds (954876037207 / 1000000000000) (238741835947 / 250000000000) x228 := by
    apply bounds_mul hx180 hx227 <;> norm_num
  let x229 : ℝ := (2 / 1)*x90
  have hx229 : Bounds (342270717081 / 250000000000) (342275399741 / 250000000000) x229 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x230 : ℝ := x198*(1 / 1)
  have hx230 : Bounds (991319537439 / 1000000000000) (991363457511 / 1000000000000) x230 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x231 : ℝ := x198*x230
  have hx231 : Bounds (245678606327 / 250000000000) (982801504889 / 1000000000000) x231 := by
    apply bounds_mul hx198 hx230 <;> norm_num
  let x232 : ℝ := x198^2
  have hx232 : Bounds (245678606327 / 250000000000) (982801504889 / 1000000000000) x232 := by
    (convert hx231 using 1; ring)
  let x233 : ℝ := x229*x232
  have hx233 : Bounds (84088592759 / 62500000000) (10512149311 / 7812500000) x233 := by
    apply bounds_mul hx229 hx232 <;> norm_num
  let x234 : ℝ := x192*(1 / 1)
  have hx234 : Bounds (1394968413 / 2000000000) (17437659 / 25000000) x234 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x235 : ℝ := x192*x234
  have hx235 : Bounds (121621054579 / 250000000000) (486515122241 / 1000000000000) x235 := by
    apply bounds_mul hx192 hx234 <;> norm_num
  let x236 : ℝ := x192*x235
  have hx236 : Bounds (169657529493 / 500000000000) (5302303 / 15625000) x236 := by
    apply bounds_mul hx192 hx235 <;> norm_num
  let x237 : ℝ := x192^3
  have hx237 : Bounds (169657529493 / 500000000000) (5302303 / 15625000) x237 := by
    (convert hx236 using 1; ring)
  let x238 : ℝ := x233*x237
  have hx238 : Bounds (456520412993 / 1000000000000) (91322123597 / 200000000000) x238 := by
    apply bounds_mul hx233 hx237 <;> norm_num
  let x239 : ℝ := x238⁻¹
  have hx239 : Bounds (438009963243 / 200000000000) (2190482553549 / 1000000000000) x239 := by
    apply bounds_inv hx238 <;> norm_num
  let x240 : ℝ := x228*x239
  have hx240 : Bounds (2091226089793 / 1000000000000) (2091839305777 / 1000000000000) x240 := by
    apply bounds_mul hx228 hx239 <;> norm_num
  let x241 : ℝ := x228/x238
  have hx241 : Bounds (2091226089793 / 1000000000000) (2091839305777 / 1000000000000) x241 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx240
  let x242 : ℝ := -x209
  have hx242 : Bounds (-186879993 / 2000000000) (-186403869 / 2000000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x243 : ℝ := (2 / 1)*x192
  have hx243 : Bounds (1394968413 / 1000000000) (17437659 / 12500000) x243 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x244 : ℝ := c*(1 / 1)
  have hx244 : Bounds (92933 / 1000000) (93169 / 1000000) x244 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x245 : ℝ := c*x244
  have hx245 : Bounds (8636542489 / 1000000000000) (8680462561 / 1000000000000) x245 := by
    apply bounds_mul hc hx244 <;> norm_num
  let x246 : ℝ := c^2
  have hx246 : Bounds (8636542489 / 1000000000000) (8680462561 / 1000000000000) x246 := by
    (convert hx245 using 1; ring)
  let x247 : ℝ := -x246
  have hx247 : Bounds (-8680462561 / 1000000000000) (-8636542489 / 1000000000000) x247 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx246
  let x248 : ℝ := x243+x247
  have hx248 : Bounds (1386287950439 / 1000000000000) (1386376177511 / 1000000000000) x248 := by
    apply bounds_add hx243 hx247 <;> norm_num
  let x249 : ℝ := x243-x246
  have hx249 : Bounds (1386287950439 / 1000000000000) (1386376177511 / 1000000000000) x249 := by
    exact hx248
  let x250 : ℝ := x242*x249
  have hx250 : Bounds (-5181719407 / 40000000000) (-64602359377 / 500000000000) x250 := by
    apply bounds_mul hx242 hx249 <;> norm_num
  let x251 : ℝ := x198⁻¹
  have hx251 : Bounds (201742356433 / 200000000000) (252189118199 / 250000000000) x251 := by
    apply bounds_inv hx198 <;> norm_num
  let x252 : ℝ := c*x251
  have hx252 : Bounds (93742612051 / 1000000000000) (46992415907 / 500000000000) x252 := by
    apply bounds_mul hc hx251 <;> norm_num
  let x253 : ℝ := c/x198
  have hx253 : Bounds (93742612051 / 1000000000000) (46992415907 / 500000000000) x253 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx252
  let x254 : ℝ := (2 / 1)*x253
  have hx254 : Bounds (93742612051 / 500000000000) (46992415907 / 250000000000) x254 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx253 <;> norm_num
  let x255 : ℝ := (2 / 1)*c
  have hx255 : Bounds (92933 / 500000) (93169 / 500000) x255 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hc <;> norm_num
  let x256 : ℝ := -x255
  have hx256 : Bounds (-93169 / 500000) (-92933 / 500000) x256 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx255
  let x257 : ℝ := x254+x256
  have hx257 : Bounds (573612051 / 500000000000) (525915907 / 250000000000) x257 := by
    apply bounds_add hx254 hx256 <;> norm_num
  let x258 : ℝ := x254-x255
  have hx258 : Bounds (573612051 / 500000000000) (525915907 / 250000000000) x258 := by
    exact hx257
  let x259 : ℝ := x180*x258
  have hx259 : Bounds (790208703 / 1000000000000) (1449051203 / 1000000000000) x259 := by
    apply bounds_mul hx180 hx258 <;> norm_num
  let x260 : ℝ := x250+x259
  have hx260 : Bounds (-16094097059 / 125000000000) (-127755667551 / 1000000000000) x260 := by
    apply bounds_add hx250 hx259 <;> norm_num
  let x261 : ℝ := (2 / 1)*x90
  have hx261 : Bounds (342270717081 / 250000000000) (342275399741 / 250000000000) x261 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x262 : ℝ := x198*(1 / 1)
  have hx262 : Bounds (991319537439 / 1000000000000) (991363457511 / 1000000000000) x262 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x263 : ℝ := x198*x262
  have hx263 : Bounds (245678606327 / 250000000000) (982801504889 / 1000000000000) x263 := by
    apply bounds_mul hx198 hx262 <;> norm_num
  let x264 : ℝ := x198^2
  have hx264 : Bounds (245678606327 / 250000000000) (982801504889 / 1000000000000) x264 := by
    (convert hx263 using 1; ring)
  let x265 : ℝ := x261*x264
  have hx265 : Bounds (84088592759 / 62500000000) (10512149311 / 7812500000) x265 := by
    apply bounds_mul hx261 hx264 <;> norm_num
  let x266 : ℝ := x192*(1 / 1)
  have hx266 : Bounds (1394968413 / 2000000000) (17437659 / 25000000) x266 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x267 : ℝ := x192*x266
  have hx267 : Bounds (121621054579 / 250000000000) (486515122241 / 1000000000000) x267 := by
    apply bounds_mul hx192 hx266 <;> norm_num
  let x268 : ℝ := x192*x267
  have hx268 : Bounds (169657529493 / 500000000000) (5302303 / 15625000) x268 := by
    apply bounds_mul hx192 hx267 <;> norm_num
  let x269 : ℝ := x192^3
  have hx269 : Bounds (169657529493 / 500000000000) (5302303 / 15625000) x269 := by
    (convert hx268 using 1; ring)
  let x270 : ℝ := x265*x269
  have hx270 : Bounds (456520412993 / 1000000000000) (91322123597 / 200000000000) x270 := by
    apply bounds_mul hx265 hx269 <;> norm_num
  let x271 : ℝ := x270⁻¹
  have hx271 : Bounds (438009963243 / 200000000000) (2190482553549 / 1000000000000) x271 := by
    apply bounds_inv hx270 <;> norm_num
  let x272 : ℝ := x260*x271
  have hx272 : Bounds (-282030710583 / 1000000000000) (-3497390953 / 12500000000) x272 := by
    apply bounds_mul hx260 hx271 <;> norm_num
  let x273 : ℝ := x260/x270
  have hx273 : Bounds (-282030710583 / 1000000000000) (-3497390953 / 12500000000) x273 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx272
  let x274 : ℝ := (4 / 1)*c
  have hx274 : Bounds (92933 / 250000) (93169 / 250000) x274 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hc <;> norm_num
  let x275 : ℝ := x198⁻¹
  have hx275 : Bounds (201742356433 / 200000000000) (252189118199 / 250000000000) x275 := by
    apply bounds_inv hx198 <;> norm_num
  let x276 : ℝ := x274*x275
  have hx276 : Bounds (374970448207 / 1000000000000) (46992415907 / 125000000000) x276 := by
    apply bounds_mul hx274 hx275 <;> norm_num
  let x277 : ℝ := x274/x198
  have hx277 : Bounds (374970448207 / 1000000000000) (46992415907 / 125000000000) x277 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx276
  let x278 : ℝ := (3 / 1)*c
  have hx278 : Bounds (278799 / 1000000) (279507 / 1000000) x278 := by
    apply bounds_mul (bounds_const ((3 / 1) : ℝ)) hc <;> norm_num
  let x279 : ℝ := x198*x192
  have hx279 : Bounds (345714860479 / 500000000000) (345741158343 / 500000000000) x279 := by
    apply bounds_mul hx198 hx192 <;> norm_num
  let x280 : ℝ := x279⁻¹
  have hx280 : Bounds (57846743199 / 40000000000) (361569646809 / 250000000000) x280 := by
    apply bounds_inv hx279 <;> norm_num
  let x281 : ℝ := x278*x280
  have hx281 : Bounds (50398794241 / 125000000000) (404244989083 / 1000000000000) x281 := by
    apply bounds_mul hx278 hx280 <;> norm_num
  let x282 : ℝ := x278/x279
  have hx282 : Bounds (50398794241 / 125000000000) (404244989083 / 1000000000000) x282 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx281
  let x283 : ℝ := -x282
  have hx283 : Bounds (-404244989083 / 1000000000000) (-50398794241 / 125000000000) x283 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx282
  let x284 : ℝ := x277+x283
  have hx284 : Bounds (-7318635219 / 250000000000) (-1703189167 / 62500000000) x284 := by
    apply bounds_add hx277 hx283 <;> norm_num
  let x285 : ℝ := x277-x282
  have hx285 : Bounds (-7318635219 / 250000000000) (-1703189167 / 62500000000) x285 := by
    exact hx284
  let x286 : ℝ := x241*x285
  have hx286 : Bounds (-61237635263 / 1000000000000) (-1139761159 / 20000000000) x286 := by
    apply bounds_mul hx241 hx285 <;> norm_num
  let x287 : ℝ := x273+x286
  have hx287 : Bounds (-171634172923 / 500000000000) (-33677933419 / 100000000000) x287 := by
    apply bounds_add hx273 hx286 <;> norm_num
  let x288 : ℝ := (2 / 1)*x192
  have hx288 : Bounds (1394968413 / 1000000000) (17437659 / 12500000) x288 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x289 : ℝ := c*(1 / 1)
  have hx289 : Bounds (92933 / 1000000) (93169 / 1000000) x289 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x290 : ℝ := c*x289
  have hx290 : Bounds (8636542489 / 1000000000000) (8680462561 / 1000000000000) x290 := by
    apply bounds_mul hc hx289 <;> norm_num
  let x291 : ℝ := c^2
  have hx291 : Bounds (8636542489 / 1000000000000) (8680462561 / 1000000000000) x291 := by
    (convert hx290 using 1; ring)
  let x292 : ℝ := -x291
  have hx292 : Bounds (-8680462561 / 1000000000000) (-8636542489 / 1000000000000) x292 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx291
  let x293 : ℝ := x288+x292
  have hx293 : Bounds (1386287950439 / 1000000000000) (1386376177511 / 1000000000000) x293 := by
    apply bounds_add hx288 hx292 <;> norm_num
  let x294 : ℝ := x288-x291
  have hx294 : Bounds (1386287950439 / 1000000000000) (1386376177511 / 1000000000000) x294 := by
    exact hx293
  let x295 : ℝ := c*x294
  have hx295 : Bounds (64415949049 / 500000000000) (129167282083 / 1000000000000) x295 := by
    apply bounds_mul hc hx294 <;> norm_num
  let x296 : ℝ := x198*(1 / 1)
  have hx296 : Bounds (991319537439 / 1000000000000) (991363457511 / 1000000000000) x296 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x297 : ℝ := x198*x296
  have hx297 : Bounds (245678606327 / 250000000000) (982801504889 / 1000000000000) x297 := by
    apply bounds_mul hx198 hx296 <;> norm_num
  let x298 : ℝ := x198^2
  have hx298 : Bounds (245678606327 / 250000000000) (982801504889 / 1000000000000) x298 := by
    (convert hx297 using 1; ring)
  let x299 : ℝ := x192*(1 / 1)
  have hx299 : Bounds (1394968413 / 2000000000) (17437659 / 25000000) x299 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x300 : ℝ := x192*x299
  have hx300 : Bounds (121621054579 / 250000000000) (486515122241 / 1000000000000) x300 := by
    apply bounds_mul hx192 hx299 <;> norm_num
  let x301 : ℝ := x192^2
  have hx301 : Bounds (121621054579 / 250000000000) (486515122241 / 1000000000000) x301 := by
    (convert hx300 using 1; ring)
  let x302 : ℝ := x298*x301
  have hx302 : Bounds (478075059023 / 1000000000000) (47814779429 / 100000000000) x302 := by
    apply bounds_mul hx298 hx301 <;> norm_num
  let x303 : ℝ := x302⁻¹
  have hx303 : Bounds (1045701780853 / 500000000000) (1045860875951 / 500000000000) x303 := by
    apply bounds_inv hx302 <;> norm_num
  let x304 : ℝ := x295*x303
  have hx304 : Bounds (269439490543 / 1000000000000) (2110796981 / 7812500000) x304 := by
    apply bounds_mul hx295 hx303 <;> norm_num
  let x305 : ℝ := x295/x302
  have hx305 : Bounds (269439490543 / 1000000000000) (2110796981 / 7812500000) x305 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx304
  let x306 : ℝ := c*x220
  have hx306 : Bounds (8691625179 / 500000000000) (17437041447 / 1000000000000) x306 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x307 : ℝ := x180+x306
  have hx307 : Bounds (70618389737 / 100000000000) (353129857011 / 500000000000) x307 := by
    apply bounds_add hx180 hx306 <;> norm_num
  let x308 : ℝ := x307*(1 / 1)
  have hx308 : Bounds (70618389737 / 100000000000) (353129857011 / 500000000000) x308 := by
    apply bounds_mul hx307 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x309 : ℝ := x307*x308
  have hx309 : Bounds (62336962113 / 125000000000) (498802783651 / 1000000000000) x309 := by
    apply bounds_mul hx307 hx308 <;> norm_num
  let x310 : ℝ := x307^2
  have hx310 : Bounds (62336962113 / 125000000000) (498802783651 / 1000000000000) x310 := by
    (convert hx309 using 1; ring)
  let x311 : ℝ := x287*x310
  have hx311 : Bounds (-10701450403 / 62500000000) (-83975202383 / 500000000000) x311 := by
    apply bounds_mul hx287 hx310 <;> norm_num
  let x312 : ℝ := (2 / 1)*x241
  have hx312 : Bounds (2091226089793 / 500000000000) (2091839305777 / 500000000000) x312 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx241 <;> norm_num
  let x313 : ℝ := c*x220
  have hx313 : Bounds (8691625179 / 500000000000) (17437041447 / 1000000000000) x313 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x314 : ℝ := x180+x313
  have hx314 : Bounds (70618389737 / 100000000000) (353129857011 / 500000000000) x314 := by
    apply bounds_add hx180 hx313 <;> norm_num
  let x315 : ℝ := x312*x314
  have hx315 : Bounds (2953580380743 / 1000000000000) (2954763659757 / 1000000000000) x315 := by
    apply bounds_mul hx312 hx314 <;> norm_num
  let x316 : ℝ := -x209
  have hx316 : Bounds (-186879993 / 2000000000) (-186403869 / 2000000000) x316 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x317 : ℝ := x220+x316
  have hx317 : Bounds (187222863 / 2000000000) (23488259 / 250000000) x317 := by
    apply bounds_add hx220 hx316 <;> norm_num
  let x318 : ℝ := x220-x209
  have hx318 : Bounds (187222863 / 2000000000) (23488259 / 250000000) x318 := by
    exact hx317
  let x319 : ℝ := x315*x318
  have hx319 : Bounds (276488887491 / 1000000000000) (277609016497 / 1000000000000) x319 := by
    apply bounds_mul hx315 hx318 <;> norm_num
  let x320 : ℝ := x311+x319
  have hx320 : Bounds (105265681043 / 1000000000000) (109658611731 / 1000000000000) x320 := by
    apply bounds_add hx311 hx319 <;> norm_num
  let x321 : ℝ := a*(1 / 1)
  have hx321 : Bounds (1849 / 10000) (37 / 200) x321 := by
    apply bounds_mul ha (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x322 : ℝ := a*x321
  have hx322 : Bounds (3418801 / 100000000) (1369 / 40000) x322 := by
    apply bounds_mul ha hx321 <;> norm_num
  let x323 : ℝ := a^2
  have hx323 : Bounds (3418801 / 100000000) (1369 / 40000) x323 := by
    (convert hx322 using 1; ring)
  let x324 : ℝ := -x323
  have hx324 : Bounds (-1369 / 40000) (-3418801 / 100000000) x324 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx323
  let x325 : ℝ := (1 / 1)+x324
  have hx325 : Bounds (38631 / 40000) (96581199 / 100000000) x325 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx324 <;> norm_num
  let x326 : ℝ := (1 / 1)-x323
  have hx326 : Bounds (38631 / 40000) (96581199 / 100000000) x326 := by
    exact hx325
  let x327 : ℝ := x326⁻¹
  have hx327 : Bounds (1035398204157 / 1000000000000) (517718930393 / 500000000000) x327 := by
    apply bounds_inv hx326 <;> norm_num
  let x328 : ℝ := (1 / 1)*x327
  have hx328 : Bounds (1035398204157 / 1000000000000) (517718930393 / 500000000000) x328 := by
    apply bounds_mul (bounds_const ((1 / 1) : ℝ)) hx327 <;> norm_num
  let x329 : ℝ := (1 / 1)/x326
  have hx329 : Bounds (1035398204157 / 1000000000000) (517718930393 / 500000000000) x329 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx328
  let x330 : ℝ := x329*x305
  have hx330 : Bounds (278977164637 / 1000000000000) (34969585769 / 125000000000) x330 := by
    apply bounds_mul hx329 hx305 <;> norm_num
  let x331 : ℝ := x320+x330
  have hx331 : Bounds (4803035571 / 12500000000) (389415297883 / 1000000000000) x331 := by
    apply bounds_add hx320 hx330 <;> norm_num
  let x332 : ℝ := x180*(1 / 1)
  have hx332 : Bounds (172200161753 / 250000000000) (27552906903 / 40000000000) x332 := by
    apply bounds_mul hx180 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x333 : ℝ := x180*x332
  have hx333 : Bounds (118611582831 / 250000000000) (237238337127 / 500000000000) x333 := by
    apply bounds_mul hx180 hx332 <;> norm_num
  let x334 : ℝ := x180^2
  have hx334 : Bounds (118611582831 / 250000000000) (237238337127 / 500000000000) x334 := by
    (convert hx333 using 1; ring)
  let x335 : ℝ := x331*x334
  have hx335 : Bounds (18230260847 / 100000000000) (46192118861 / 250000000000) x335 := by
    apply bounds_mul hx331 hx334 <;> norm_num
  let x336 : ℝ := x90*x192
  have hx336 : Bounds (238728419511 / 500000000000) (238739268191 / 500000000000) x336 := by
    apply bounds_mul hx90 hx192 <;> norm_num
  let x337 : ℝ := x336⁻¹
  have hx337 : Bounds (1047167489011 / 500000000000) (418886030431 / 200000000000) x337 := by
    apply bounds_inv hx336 <;> norm_num
  let x338 : ℝ := x335*x337
  have hx338 : Bounds (381802729503 / 1000000000000) (193492333069 / 500000000000) x338 := by
    apply bounds_mul hx335 hx337 <;> norm_num
  let x339 : ℝ := x335/x336
  have hx339 : Bounds (381802729503 / 1000000000000) (193492333069 / 500000000000) x339 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx338
  have hu : x339 < (3653882551473364697152287469 / 9327928000277601000000000000) := lt_of_le_of_lt hx339.2 (by norm_num)
  simpa +zetaDelta only [ScFormula,Kprime,K,Mprime,SmallMean.A,biasB,div_one,pow_two] using hu

open GeneralCK.Reflection
/-- Uniform derivative enclosure including input boxes with z=0. -/
theorem derivative_bound_349 {a z s : ℝ}
    (ha : a ∈ Set.Icc ((1849 / 10000):ℝ) ((37 / 200)))
    (hz : z ∈ Set.Icc (0:ℝ) (1/1000))
    (hs : s ∈ Set.Ioo (a*(1-z)/2) (a*(1+z)/2)) :
    P a ((biasE a+biasE (a*z))/2) s ≤ (3653882551473364697152287469 / 9327928000277601000000000000) := by
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
  have hsl : (1847151 / 20000000) ≤ s := by
    have h := mul_le_mul ha.1 (show (999/1000:ℝ) ≤ 1-z by linarith [hz.2])
      (by norm_num : (0:ℝ) ≤ 999/1000) ha0.le
    nlinarith [hs.1]
  have hsu : s ≤ (37037 / 400000) := by
    have h := mul_le_mul ha.2 (show 1+z ≤ (1001/1000:ℝ) by linarith [hz.2])
      (by linarith [hz.1] : 0 ≤ 1+z) (by norm_num : (0:ℝ) ≤ (37 / 200))
    nlinarith [hs.2]
  have hy := div_pos he hs0
  have hc := biasContact_mem hy
  have heq : biasE (biasContact (((biasE a+biasE (a*z))/2)/s)) =
      (((biasE a+biasE (a*z))/2)/s)*biasContact (((biasE a+biasE (a*z))/2)/s) := by
    exact (div_eq_iff hc.1.ne').mp (biasR_biasContact hy)
  have hb := derivative_leaf_349 a z s _ ha hz ⟨hsl,hsu⟩ hc.1.le hc.2.le heq
  rw [P_eq_formula ha0 ha1 he hs0]
  exact hb.le

/-- Checked low-ratio strip: includes arbitrarily small positive z. -/
theorem curvature_leaf_349 {a z : ℝ}
    (ha : a ∈ Set.Icc ((1849 / 10000):ℝ) ((37 / 200)))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < curvature a (a*z) := by
  have ha0 : 0 < a := by linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  apply curvature_pos_of_derivative_bound ha0 ha1 hz.1 (by linarith [hz.2])
    (fun s hs => derivative_bound_349 ha ⟨hz.1.le,hz.2⟩ hs) (M := (3653882551473364697152287469 / 9327928000277601000000000000))
  exact lt_of_lt_of_le (by norm_num : (3653882551473364697152287469 / 9327928000277601000000000000) < 2*((1849 / 10000):ℝ)/(1-((1849 / 10000):ℝ)^2)^2)
    (base_mono (by norm_num) ha.1 ha1)

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Cell0350 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
theorem derivative_leaf_350 (a z s c : ℝ)
    (ha : Bounds (37 / 200) (1851 / 10000) a) (hz : Bounds 0 (1/1000) z)
    (hs : Bounds (36963 / 400000) (1852851 / 20000000) s) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (heq : biasE c = (((biasE a+biasE (a*z))/2)/s)*c) :
    ScFormula c a ((biasE a+biasE (a*z))/2)*(biasE c)^2 /
      (((biasE a+biasE (a*z))/2)*biasB c) < (1169852961734184398083 / 2984708322000000000000) := by
  let x0 : ℝ := Real.log (2 / 1)
  have hx0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x0 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x1 : ℝ := (1 / 1)+(1851 / 10000)
  have hx1 : Bounds (11851 / 10000) (11851 / 10000) x1 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1851 / 10000) : ℝ)) <;> norm_num
  let x2 : ℝ := (1 / 1)+(1851 / 10000)
  have hx2 : Bounds (11851 / 10000) (11851 / 10000) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1851 / 10000) : ℝ)) <;> norm_num
  let x3 : ℝ := Real.log x2
  have hx3 : Bounds (169827159 / 1000000000) (4245679 / 25000000) x3 := by
    exact bounds_log hx2 (by norm_num) (by simpa only [div_one] using reflection_log_4870.1) (by simpa only [div_one] using reflection_log_4870.2)
  let x4 : ℝ := x1*x3
  have hx4 : Bounds (20126216613 / 100000000000) (50315541829 / 250000000000) x4 := by
    apply bounds_mul hx1 hx3 <;> norm_num
  let x5 : ℝ := -(1851 / 10000)
  have hx5 : Bounds (-1851 / 10000) (-1851 / 10000) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1851 / 10000) : ℝ))
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (8149 / 10000) (8149 / 10000) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-(1851 / 10000)
  have hx7 : Bounds (8149 / 10000) (8149 / 10000) x7 := by
    exact hx6
  let x8 : ℝ := -(1851 / 10000)
  have hx8 : Bounds (-1851 / 10000) (-1851 / 10000) x8 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1851 / 10000) : ℝ))
  let x9 : ℝ := (1 / 1)+x8
  have hx9 : Bounds (8149 / 10000) (8149 / 10000) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx8 <;> norm_num
  let x10 : ℝ := (1 / 1)-(1851 / 10000)
  have hx10 : Bounds (8149 / 10000) (8149 / 10000) x10 := by
    exact hx9
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (-204689873 / 1000000000) (-12793117 / 62500000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_4871.1) (by simpa only [div_one] using reflection_log_4871.2)
  let x12 : ℝ := x7*x11
  have hx12 : Bounds (-41700444377 / 250000000000) (-41700444173 / 250000000000) x12 := by
    apply bounds_mul hx7 hx11 <;> norm_num
  let x13 : ℝ := x4+x12
  have hx13 : Bounds (17230194311 / 500000000000) (1076887207 / 31250000000) x13 := by
    apply bounds_add hx4 hx12 <;> norm_num
  let x14 : ℝ := (2 / 1)⁻¹
  have hx14 : Bounds (1 / 2) (1 / 2) x14 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x15 : ℝ := x13*x14
  have hx15 : Bounds (17230194311 / 1000000000000) (1076887207 / 62500000000) x15 := by
    apply bounds_mul hx13 hx14 <;> norm_num
  let x16 : ℝ := x13/(2 / 1)
  have hx16 : Bounds (17230194311 / 1000000000000) (1076887207 / 62500000000) x16 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx15
  let x17 : ℝ := -x16
  have hx17 : Bounds (-1076887207 / 62500000000) (-17230194311 / 1000000000000) x17 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx16
  let x18 : ℝ := x0+x17
  have hx18 : Bounds (42244811543 / 62500000000) (675916986689 / 1000000000000) x18 := by
    apply bounds_add hx0 hx17 <;> norm_num
  let x19 : ℝ := x0-x16
  have hx19 : Bounds (42244811543 / 62500000000) (675916986689 / 1000000000000) x19 := by
    exact hx18
  let x20 : ℝ := biasE (1851 / 10000)
  have hx20 : Bounds (42244811543 / 62500000000) (675916986689 / 1000000000000) x20 := by
    simpa +zetaDelta only [biasE, div_one] using hx19
  let x21 : ℝ := Real.log (2 / 1)
  have hx21 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x21 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x22 : ℝ := (1 / 1)+(37 / 200)
  have hx22 : Bounds (237 / 200) (237 / 200) x22 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((37 / 200) : ℝ)) <;> norm_num
  let x23 : ℝ := (1 / 1)+(37 / 200)
  have hx23 : Bounds (237 / 200) (237 / 200) x23 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((37 / 200) : ℝ)) <;> norm_num
  let x24 : ℝ := Real.log x23
  have hx24 : Bounds (84871387 / 500000000) (6789711 / 40000000) x24 := by
    exact bounds_log hx23 (by norm_num) (by simpa only [div_one] using reflection_log_4856.1) (by simpa only [div_one] using reflection_log_4856.2)
  let x25 : ℝ := x22*x24
  have hx25 : Bounds (20114518719 / 100000000000) (1609161507 / 8000000000) x25 := by
    apply bounds_mul hx22 hx24 <;> norm_num
  let x26 : ℝ := -(37 / 200)
  have hx26 : Bounds (-37 / 200) (-37 / 200) x26 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((37 / 200) : ℝ))
  let x27 : ℝ := (1 / 1)+x26
  have hx27 : Bounds (163 / 200) (163 / 200) x27 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx26 <;> norm_num
  let x28 : ℝ := (1 / 1)-(37 / 200)
  have hx28 : Bounds (163 / 200) (163 / 200) x28 := by
    exact hx27
  let x29 : ℝ := -(37 / 200)
  have hx29 : Bounds (-37 / 200) (-37 / 200) x29 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((37 / 200) : ℝ))
  let x30 : ℝ := (1 / 1)+x29
  have hx30 : Bounds (163 / 200) (163 / 200) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx29 <;> norm_num
  let x31 : ℝ := (1 / 1)-(37 / 200)
  have hx31 : Bounds (163 / 200) (163 / 200) x31 := by
    exact hx30
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (-102283583 / 500000000) (-40913433 / 200000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_4857.1) (by simpa only [div_one] using reflection_log_4857.2)
  let x33 : ℝ := x28*x32
  have hx33 : Bounds (-16672224029 / 100000000000) (-6668889579 / 40000000000) x33 := by
    apply bounds_mul hx28 hx32 <;> norm_num
  let x34 : ℝ := x25+x33
  have hx34 : Bounds (344229469 / 10000000000) (344229489 / 10000000000) x34 := by
    apply bounds_add hx25 hx33 <;> norm_num
  let x35 : ℝ := (2 / 1)⁻¹
  have hx35 : Bounds (1 / 2) (1 / 2) x35 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x36 : ℝ := x34*x35
  have hx36 : Bounds (344229469 / 20000000000) (344229489 / 20000000000) x36 := by
    apply bounds_mul hx34 hx35 <;> norm_num
  let x37 : ℝ := x34/(2 / 1)
  have hx37 : Bounds (344229469 / 20000000000) (344229489 / 20000000000) x37 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx36
  let x38 : ℝ := -x37
  have hx38 : Bounds (-344229489 / 20000000000) (-344229469 / 20000000000) x38 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx37
  let x39 : ℝ := x21+x38
  have hx39 : Bounds (13518714111 / 20000000000) (13518714151 / 20000000000) x39 := by
    apply bounds_add hx21 hx38 <;> norm_num
  let x40 : ℝ := x21-x37
  have hx40 : Bounds (13518714111 / 20000000000) (13518714151 / 20000000000) x40 := by
    exact hx39
  let x41 : ℝ := biasE (37 / 200)
  have hx41 : Bounds (13518714111 / 20000000000) (13518714151 / 20000000000) x41 := by
    simpa +zetaDelta only [biasE, div_one] using hx40
  let x42 : ℝ := biasE a
  have hx42 : Bounds (42244811543 / 62500000000) (13518714151 / 20000000000) x42 := by
    exact bounds_biasE ha (by norm_num) (by norm_num) hx20.1 hx41.2
  let x43 : ℝ := a*z
  have hx43 : Bounds (0 / 1) (1851 / 10000000) x43 := by
    apply bounds_mul ha hz <;> norm_num
  let x44 : ℝ := Real.log (2 / 1)
  have hx44 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x44 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x45 : ℝ := (1 / 1)+(1851 / 10000000)
  have hx45 : Bounds (10001851 / 10000000) (10001851 / 10000000) x45 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1851 / 10000000) : ℝ)) <;> norm_num
  let x46 : ℝ := (1 / 1)+(1851 / 10000000)
  have hx46 : Bounds (10001851 / 10000000) (10001851 / 10000000) x46 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1851 / 10000000) : ℝ)) <;> norm_num
  let x47 : ℝ := Real.log x46
  have hx47 : Bounds (92541 / 500000000) (185083 / 1000000000) x47 := by
    exact bounds_log hx46 (by norm_num) (by simpa only [div_one] using reflection_log_4872.1) (by simpa only [div_one] using reflection_log_4872.2)
  let x48 : ℝ := x45*x47
  have hx48 : Bounds (92558129 / 500000000000) (185117259 / 1000000000000) x48 := by
    apply bounds_mul hx45 hx47 <;> norm_num
  let x49 : ℝ := -(1851 / 10000000)
  have hx49 : Bounds (-1851 / 10000000) (-1851 / 10000000) x49 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1851 / 10000000) : ℝ))
  let x50 : ℝ := (1 / 1)+x49
  have hx50 : Bounds (9998149 / 10000000) (9998149 / 10000000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx49 <;> norm_num
  let x51 : ℝ := (1 / 1)-(1851 / 10000000)
  have hx51 : Bounds (9998149 / 10000000) (9998149 / 10000000) x51 := by
    exact hx50
  let x52 : ℝ := -(1851 / 10000000)
  have hx52 : Bounds (-1851 / 10000000) (-1851 / 10000000) x52 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1851 / 10000000) : ℝ))
  let x53 : ℝ := (1 / 1)+x52
  have hx53 : Bounds (9998149 / 10000000) (9998149 / 10000000) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx52 <;> norm_num
  let x54 : ℝ := (1 / 1)-(1851 / 10000000)
  have hx54 : Bounds (9998149 / 10000000) (9998149 / 10000000) x54 := by
    exact hx53
  let x55 : ℝ := Real.log x54
  have hx55 : Bounds (-92559 / 500000000) (-185117 / 1000000000) x55 := by
    exact bounds_log hx54 (by norm_num) (by simpa only [div_one] using reflection_log_4873.1) (by simpa only [div_one] using reflection_log_4873.2)
  let x56 : ℝ := x51*x55
  have hx56 : Bounds (-37016747 / 200000000000) (-92541367 / 500000000000) x56 := by
    apply bounds_mul hx51 hx55 <;> norm_num
  let x57 : ℝ := x48+x56
  have hx57 : Bounds (32523 / 1000000000000) (1381 / 40000000000) x57 := by
    apply bounds_add hx48 hx56 <;> norm_num
  let x58 : ℝ := (2 / 1)⁻¹
  have hx58 : Bounds (1 / 2) (1 / 2) x58 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x59 : ℝ := x57*x58
  have hx59 : Bounds (16261 / 1000000000000) (17263 / 1000000000000) x59 := by
    apply bounds_mul hx57 hx58 <;> norm_num
  let x60 : ℝ := x57/(2 / 1)
  have hx60 : Bounds (16261 / 1000000000000) (17263 / 1000000000000) x60 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx59
  let x61 : ℝ := -x60
  have hx61 : Bounds (-17263 / 1000000000000) (-16261 / 1000000000000) x61 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx60
  let x62 : ℝ := x44+x61
  have hx62 : Bounds (693147162737 / 1000000000000) (693147164739 / 1000000000000) x62 := by
    apply bounds_add hx44 hx61 <;> norm_num
  let x63 : ℝ := x44-x60
  have hx63 : Bounds (693147162737 / 1000000000000) (693147164739 / 1000000000000) x63 := by
    exact hx62
  let x64 : ℝ := biasE (1851 / 10000000)
  have hx64 : Bounds (693147162737 / 1000000000000) (693147164739 / 1000000000000) x64 := by
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
  have hx86 : Bounds (693147162737 / 1000000000000) (693147181 / 1000000000) x86 := by
    exact bounds_biasE hx43 (by norm_num) (by norm_num) hx64.1 hx85.2
  let x87 : ℝ := x42+x86
  have hx87 : Bounds (54762565897 / 40000000000) (27381657771 / 20000000000) x87 := by
    apply bounds_add hx42 hx86 <;> norm_num
  let x88 : ℝ := (2 / 1)⁻¹
  have hx88 : Bounds (1 / 2) (1 / 2) x88 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x89 : ℝ := x87*x88
  have hx89 : Bounds (42783254607 / 62500000000) (27381657771 / 40000000000) x89 := by
    apply bounds_mul hx87 hx88 <;> norm_num
  let x90 : ℝ := x87/(2 / 1)
  have hx90 : Bounds (42783254607 / 62500000000) (27381657771 / 40000000000) x90 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx89
  let x91 : ℝ := s⁻¹
  have hx91 : Bounds (10794176110221 / 1000000000000) (2164326488651 / 200000000000) x91 := by
    apply bounds_inv hs <;> norm_num
  let x92 : ℝ := x90*x91
  have hx92 : Bounds (3694479878371 / 500000000000) (7407855902119 / 1000000000000) x92 := by
    apply bounds_mul hx90 hx91 <;> norm_num
  let x93 : ℝ := x90/s
  have hx93 : Bounds (3694479878371 / 500000000000) (7407855902119 / 1000000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(11623 / 125000)
  have hx95 : Bounds (136623 / 125000) (136623 / 125000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((11623 / 125000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(11623 / 125000)
  have hx96 : Bounds (136623 / 125000) (136623 / 125000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((11623 / 125000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (8891157 / 100000000) (88911571 / 1000000000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_4874.1) (by simpa only [div_one] using reflection_log_4874.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (3036841357 / 31250000000) (48589462259 / 500000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(11623 / 125000)
  have hx99 : Bounds (-11623 / 125000) (-11623 / 125000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((11623 / 125000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (113377 / 125000) (113377 / 125000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(11623 / 125000)
  have hx101 : Bounds (113377 / 125000) (113377 / 125000) x101 := by
    exact hx100
  let x102 : ℝ := -(11623 / 125000)
  have hx102 : Bounds (-11623 / 125000) (-11623 / 125000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((11623 / 125000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (113377 / 125000) (113377 / 125000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(11623 / 125000)
  have hx104 : Bounds (113377 / 125000) (113377 / 125000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-97595189 / 1000000000) (-24398797 / 250000000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_4875.1) (by simpa only [div_one] using reflection_log_4875.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-88520397947 / 1000000000000) (-88520397039 / 1000000000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (8658525477 / 1000000000000) (8658527479 / 1000000000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (2164631369 / 500000000000) (216463187 / 50000000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (2164631369 / 500000000000) (216463187 / 50000000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-216463187 / 50000000000) (-2164631369 / 500000000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (34440895813 / 50000000000) (344408959131 / 500000000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (34440895813 / 50000000000) (344408959131 / 500000000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (11623 / 125000)
  have hx114 : Bounds (34440895813 / 50000000000) (344408959131 / 500000000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(4661 / 50000)
  have hx116 : Bounds (54661 / 50000) (54661 / 50000) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((4661 / 50000) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(4661 / 50000)
  have hx117 : Bounds (54661 / 50000) (54661 / 50000) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((4661 / 50000) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (89127469 / 1000000000) (8912747 / 100000000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_4876.1) (by simpa only [div_one] using reflection_log_4876.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (4871796583 / 50000000000) (48717966377 / 500000000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(4661 / 50000)
  have hx120 : Bounds (-4661 / 50000) (-4661 / 50000) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((4661 / 50000) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (45339 / 50000) (45339 / 50000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(4661 / 50000)
  have hx122 : Bounds (45339 / 50000) (45339 / 50000) x122 := by
    exact hx121
  let x123 : ℝ := -(4661 / 50000)
  have hx123 : Bounds (-4661 / 50000) (-4661 / 50000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((4661 / 50000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (45339 / 50000) (45339 / 50000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(4661 / 50000)
  have hx125 : Bounds (45339 / 50000) (45339 / 50000) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-97855417 / 1000000000) (-12231927 / 125000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_4877.1) (by simpa only [div_one] using reflection_log_4877.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-22183333757 / 250000000000) (-2218333353 / 25000000000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (1087824579 / 125000000000) (4351299317 / 500000000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (1087824579 / 250000000000) (4351299317 / 1000000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (1087824579 / 250000000000) (4351299317 / 1000000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-4351299317 / 1000000000000) (-1087824579 / 250000000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (688795880683 / 1000000000000) (172198970671 / 250000000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (688795880683 / 1000000000000) (172198970671 / 250000000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (4661 / 50000)
  have hx135 : Bounds (688795880683 / 1000000000000) (172198970671 / 250000000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(11623 / 125000)
  have hx136 : Bounds (34352751701 / 50000000000) (688812073203 / 1000000000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((11623 / 125000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(4661 / 50000)
  have hx137 : Bounds (688798828523 / 1000000000000) (172640081799 / 250000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((4661 / 50000) : ℝ)) <;> norm_num
  have hc : Bounds (11623 / 125000) (4661 / 50000) c := by
    apply contact_bracket hc0 hc1 (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x93 by linarith [hx93.1])
      (show biasE c = x93*c by simpa +zetaDelta only [div_one] using heq)
    · have h1 : x93*(11623 / 125000) ≤ (688812073203 / 1000000000000) := hx136.2
      have h2 : (34440895813 / 50000000000) ≤ biasE (11623 / 125000) := hx114.1
      linarith
    · have h1 : biasE (4661 / 50000) ≤ (172198970671 / 250000000000) := hx135.2
      have h2 : (688798828523 / 1000000000000) ≤ x93*(4661 / 50000) := hx137.1
      linarith
  let x138 : ℝ := Real.log (2 / 1)
  have hx138 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x138 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x139 : ℝ := (1 / 1)+(4661 / 50000)
  have hx139 : Bounds (54661 / 50000) (54661 / 50000) x139 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((4661 / 50000) : ℝ)) <;> norm_num
  let x140 : ℝ := (1 / 1)+(4661 / 50000)
  have hx140 : Bounds (54661 / 50000) (54661 / 50000) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((4661 / 50000) : ℝ)) <;> norm_num
  let x141 : ℝ := Real.log x140
  have hx141 : Bounds (89127469 / 1000000000) (8912747 / 100000000) x141 := by
    exact bounds_log hx140 (by norm_num) (by simpa only [div_one] using reflection_log_4876.1) (by simpa only [div_one] using reflection_log_4876.2)
  let x142 : ℝ := x139*x141
  have hx142 : Bounds (4871796583 / 50000000000) (48717966377 / 500000000000) x142 := by
    apply bounds_mul hx139 hx141 <;> norm_num
  let x143 : ℝ := -(4661 / 50000)
  have hx143 : Bounds (-4661 / 50000) (-4661 / 50000) x143 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((4661 / 50000) : ℝ))
  let x144 : ℝ := (1 / 1)+x143
  have hx144 : Bounds (45339 / 50000) (45339 / 50000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx143 <;> norm_num
  let x145 : ℝ := (1 / 1)-(4661 / 50000)
  have hx145 : Bounds (45339 / 50000) (45339 / 50000) x145 := by
    exact hx144
  let x146 : ℝ := -(4661 / 50000)
  have hx146 : Bounds (-4661 / 50000) (-4661 / 50000) x146 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((4661 / 50000) : ℝ))
  let x147 : ℝ := (1 / 1)+x146
  have hx147 : Bounds (45339 / 50000) (45339 / 50000) x147 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx146 <;> norm_num
  let x148 : ℝ := (1 / 1)-(4661 / 50000)
  have hx148 : Bounds (45339 / 50000) (45339 / 50000) x148 := by
    exact hx147
  let x149 : ℝ := Real.log x148
  have hx149 : Bounds (-97855417 / 1000000000) (-12231927 / 125000000) x149 := by
    exact bounds_log hx148 (by norm_num) (by simpa only [div_one] using reflection_log_4877.1) (by simpa only [div_one] using reflection_log_4877.2)
  let x150 : ℝ := x145*x149
  have hx150 : Bounds (-22183333757 / 250000000000) (-2218333353 / 25000000000) x150 := by
    apply bounds_mul hx145 hx149 <;> norm_num
  let x151 : ℝ := x142+x150
  have hx151 : Bounds (1087824579 / 125000000000) (4351299317 / 500000000000) x151 := by
    apply bounds_add hx142 hx150 <;> norm_num
  let x152 : ℝ := (2 / 1)⁻¹
  have hx152 : Bounds (1 / 2) (1 / 2) x152 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x153 : ℝ := x151*x152
  have hx153 : Bounds (1087824579 / 250000000000) (4351299317 / 1000000000000) x153 := by
    apply bounds_mul hx151 hx152 <;> norm_num
  let x154 : ℝ := x151/(2 / 1)
  have hx154 : Bounds (1087824579 / 250000000000) (4351299317 / 1000000000000) x154 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx153
  let x155 : ℝ := -x154
  have hx155 : Bounds (-4351299317 / 1000000000000) (-1087824579 / 250000000000) x155 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx154
  let x156 : ℝ := x138+x155
  have hx156 : Bounds (688795880683 / 1000000000000) (172198970671 / 250000000000) x156 := by
    apply bounds_add hx138 hx155 <;> norm_num
  let x157 : ℝ := x138-x154
  have hx157 : Bounds (688795880683 / 1000000000000) (172198970671 / 250000000000) x157 := by
    exact hx156
  let x158 : ℝ := biasE (4661 / 50000)
  have hx158 : Bounds (688795880683 / 1000000000000) (172198970671 / 250000000000) x158 := by
    simpa +zetaDelta only [biasE, div_one] using hx157
  let x159 : ℝ := Real.log (2 / 1)
  have hx159 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x159 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x160 : ℝ := (1 / 1)+(11623 / 125000)
  have hx160 : Bounds (136623 / 125000) (136623 / 125000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((11623 / 125000) : ℝ)) <;> norm_num
  let x161 : ℝ := (1 / 1)+(11623 / 125000)
  have hx161 : Bounds (136623 / 125000) (136623 / 125000) x161 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((11623 / 125000) : ℝ)) <;> norm_num
  let x162 : ℝ := Real.log x161
  have hx162 : Bounds (8891157 / 100000000) (88911571 / 1000000000) x162 := by
    exact bounds_log hx161 (by norm_num) (by simpa only [div_one] using reflection_log_4874.1) (by simpa only [div_one] using reflection_log_4874.2)
  let x163 : ℝ := x160*x162
  have hx163 : Bounds (3036841357 / 31250000000) (48589462259 / 500000000000) x163 := by
    apply bounds_mul hx160 hx162 <;> norm_num
  let x164 : ℝ := -(11623 / 125000)
  have hx164 : Bounds (-11623 / 125000) (-11623 / 125000) x164 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((11623 / 125000) : ℝ))
  let x165 : ℝ := (1 / 1)+x164
  have hx165 : Bounds (113377 / 125000) (113377 / 125000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx164 <;> norm_num
  let x166 : ℝ := (1 / 1)-(11623 / 125000)
  have hx166 : Bounds (113377 / 125000) (113377 / 125000) x166 := by
    exact hx165
  let x167 : ℝ := -(11623 / 125000)
  have hx167 : Bounds (-11623 / 125000) (-11623 / 125000) x167 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((11623 / 125000) : ℝ))
  let x168 : ℝ := (1 / 1)+x167
  have hx168 : Bounds (113377 / 125000) (113377 / 125000) x168 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx167 <;> norm_num
  let x169 : ℝ := (1 / 1)-(11623 / 125000)
  have hx169 : Bounds (113377 / 125000) (113377 / 125000) x169 := by
    exact hx168
  let x170 : ℝ := Real.log x169
  have hx170 : Bounds (-97595189 / 1000000000) (-24398797 / 250000000) x170 := by
    exact bounds_log hx169 (by norm_num) (by simpa only [div_one] using reflection_log_4875.1) (by simpa only [div_one] using reflection_log_4875.2)
  let x171 : ℝ := x166*x170
  have hx171 : Bounds (-88520397947 / 1000000000000) (-88520397039 / 1000000000000) x171 := by
    apply bounds_mul hx166 hx170 <;> norm_num
  let x172 : ℝ := x163+x171
  have hx172 : Bounds (8658525477 / 1000000000000) (8658527479 / 1000000000000) x172 := by
    apply bounds_add hx163 hx171 <;> norm_num
  let x173 : ℝ := (2 / 1)⁻¹
  have hx173 : Bounds (1 / 2) (1 / 2) x173 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x174 : ℝ := x172*x173
  have hx174 : Bounds (2164631369 / 500000000000) (216463187 / 50000000000) x174 := by
    apply bounds_mul hx172 hx173 <;> norm_num
  let x175 : ℝ := x172/(2 / 1)
  have hx175 : Bounds (2164631369 / 500000000000) (216463187 / 50000000000) x175 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx174
  let x176 : ℝ := -x175
  have hx176 : Bounds (-216463187 / 50000000000) (-2164631369 / 500000000000) x176 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx175
  let x177 : ℝ := x159+x176
  have hx177 : Bounds (34440895813 / 50000000000) (344408959131 / 500000000000) x177 := by
    apply bounds_add hx159 hx176 <;> norm_num
  let x178 : ℝ := x159-x175
  have hx178 : Bounds (34440895813 / 50000000000) (344408959131 / 500000000000) x178 := by
    exact hx177
  let x179 : ℝ := biasE (11623 / 125000)
  have hx179 : Bounds (34440895813 / 50000000000) (344408959131 / 500000000000) x179 := by
    simpa +zetaDelta only [biasE, div_one] using hx178
  let x180 : ℝ := biasE c
  have hx180 : Bounds (688795880683 / 1000000000000) (344408959131 / 500000000000) x180 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx158.1 hx179.2
  let x181 : ℝ := Real.log (2 / 1)
  have hx181 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x181 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x182 : ℝ := c*c
  have hx182 : Bounds (135094129 / 15625000000) (21724921 / 2500000000) x182 := by
    apply bounds_mul hc hc <;> norm_num
  let x183 : ℝ := -x182
  have hx183 : Bounds (-21724921 / 2500000000) (-135094129 / 15625000000) x183 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx182
  let x184 : ℝ := (1 / 1)+x183
  have hx184 : Bounds (2478275079 / 2500000000) (15489905871 / 15625000000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx183 <;> norm_num
  let x185 : ℝ := (1 / 1)-x182
  have hx185 : Bounds (2478275079 / 2500000000) (15489905871 / 15625000000) x185 := by
    exact hx184
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (-8727947 / 1000000000) (-8683617 / 1000000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_4878.1) (by simpa only [div_one] using reflection_log_4879.2)
  let x187 : ℝ := (2 / 1)⁻¹
  have hx187 : Bounds (1 / 2) (1 / 2) x187 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x188 : ℝ := x186*x187
  have hx188 : Bounds (-8727947 / 2000000000) (-8683617 / 2000000000) x188 := by
    apply bounds_mul hx186 hx187 <;> norm_num
  let x189 : ℝ := x186/(2 / 1)
  have hx189 : Bounds (-8727947 / 2000000000) (-8683617 / 2000000000) x189 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx188
  let x190 : ℝ := -x189
  have hx190 : Bounds (8683617 / 2000000000) (8727947 / 2000000000) x190 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx189
  let x191 : ℝ := x181+x190
  have hx191 : Bounds (1394977977 / 2000000000) (1395022309 / 2000000000) x191 := by
    apply bounds_add hx181 hx190 <;> norm_num
  let x192 : ℝ := x181-x189
  have hx192 : Bounds (1394977977 / 2000000000) (1395022309 / 2000000000) x192 := by
    exact hx191
  let x193 : ℝ := c*(1 / 1)
  have hx193 : Bounds (11623 / 125000) (4661 / 50000) x193 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x194 : ℝ := c*x193
  have hx194 : Bounds (135094129 / 15625000000) (21724921 / 2500000000) x194 := by
    apply bounds_mul hc hx193 <;> norm_num
  let x195 : ℝ := c^2
  have hx195 : Bounds (135094129 / 15625000000) (21724921 / 2500000000) x195 := by
    (convert hx194 using 1; ring)
  let x196 : ℝ := -x195
  have hx196 : Bounds (-21724921 / 2500000000) (-135094129 / 15625000000) x196 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx195
  let x197 : ℝ := (1 / 1)+x196
  have hx197 : Bounds (2478275079 / 2500000000) (15489905871 / 15625000000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx196 <;> norm_num
  let x198 : ℝ := (1 / 1)-x195
  have hx198 : Bounds (2478275079 / 2500000000) (15489905871 / 15625000000) x198 := by
    exact hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (136623 / 125000) (54661 / 50000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-4661 / 50000) (-11623 / 125000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (45339 / 50000) (113377 / 125000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (45339 / 50000) (113377 / 125000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (1102516383393 / 1000000000000) (220560665211 / 200000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (602516383393 / 500000000000) (120560665211 / 100000000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (602516383393 / 500000000000) (120560665211 / 100000000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (93253379 / 500000000) (93491443 / 500000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_4880.1) (by simpa only [div_one] using reflection_log_4881.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (93253379 / 1000000000) (93491443 / 1000000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (93253379 / 1000000000) (93491443 / 1000000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (1 / 1)+a
  have hx210 : Bounds (237 / 200) (11851 / 10000) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) ha <;> norm_num
  let x211 : ℝ := -a
  have hx211 : Bounds (-1851 / 10000) (-37 / 200) x211 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg ha
  let x212 : ℝ := (1 / 1)+x211
  have hx212 : Bounds (8149 / 10000) (163 / 200) x212 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx211 <;> norm_num
  let x213 : ℝ := (1 / 1)-a
  have hx213 : Bounds (8149 / 10000) (163 / 200) x213 := by
    exact hx212
  let x214 : ℝ := x213⁻¹
  have hx214 : Bounds (122699386503 / 100000000000) (12271444349 / 10000000000) x214 := by
    apply bounds_inv hx213 <;> norm_num
  let x215 : ℝ := x210*x214
  have hx215 : Bounds (72699386503 / 50000000000) (7271444349 / 5000000000) x215 := by
    apply bounds_mul hx210 hx214 <;> norm_num
  let x216 : ℝ := x210/x213
  have hx216 : Bounds (72699386503 / 50000000000) (7271444349 / 5000000000) x216 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx215
  let x217 : ℝ := Real.log x216
  have hx217 : Bounds (18715497 / 50000000) (46814629 / 125000000) x217 := by
    exact bounds_log hx216 (by norm_num) (by simpa only [div_one] using reflection_log_4882.1) (by simpa only [div_one] using reflection_log_4883.2)
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (18715497 / 100000000) (46814629 / 250000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (18715497 / 100000000) (46814629 / 250000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := (2 / 1)*x192
  have hx221 : Bounds (1394977977 / 1000000000) (1395022309 / 1000000000) x221 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x222 : ℝ := c*(1 / 1)
  have hx222 : Bounds (11623 / 125000) (4661 / 50000) x222 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x223 : ℝ := c*x222
  have hx223 : Bounds (135094129 / 15625000000) (21724921 / 2500000000) x223 := by
    apply bounds_mul hc hx222 <;> norm_num
  let x224 : ℝ := c^2
  have hx224 : Bounds (135094129 / 15625000000) (21724921 / 2500000000) x224 := by
    (convert hx223 using 1; ring)
  let x225 : ℝ := -x224
  have hx225 : Bounds (-21724921 / 2500000000) (-135094129 / 15625000000) x225 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx224
  let x226 : ℝ := x221+x225
  have hx226 : Bounds (6931440043 / 5000000000) (173297035593 / 125000000000) x226 := by
    apply bounds_add hx221 hx225 <;> norm_num
  let x227 : ℝ := x221-x224
  have hx227 : Bounds (6931440043 / 5000000000) (173297035593 / 125000000000) x227 := by
    exact hx226
  let x228 : ℝ := x180*x227
  have hx228 : Bounds (954869469763 / 1000000000000) (477480413193 / 500000000000) x228 := by
    apply bounds_mul hx180 hx227 <;> norm_num
  let x229 : ℝ := (2 / 1)*x90
  have hx229 : Bounds (42783254607 / 31250000000) (27381657771 / 20000000000) x229 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x230 : ℝ := x198*(1 / 1)
  have hx230 : Bounds (2478275079 / 2500000000) (15489905871 / 15625000000) x230 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x231 : ℝ := x198*x230
  have hx231 : Bounds (786156463 / 800000000) (122847838153 / 125000000000) x231 := by
    apply bounds_mul hx198 hx230 <;> norm_num
  let x232 : ℝ := x198^2
  have hx232 : Bounds (786156463 / 800000000) (122847838153 / 125000000000) x232 := by
    (convert hx231 using 1; ring)
  let x233 : ℝ := x229*x232
  have hx233 : Bounds (672686642349 / 500000000000) (672755492443 / 500000000000) x233 := by
    apply bounds_mul hx229 hx232 <;> norm_num
  let x234 : ℝ := x192*(1 / 1)
  have hx234 : Bounds (1394977977 / 2000000000) (1395022309 / 2000000000) x234 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x235 : ℝ := x192*x234
  have hx235 : Bounds (243245444539 / 500000000000) (121630452663 / 250000000000) x235 := by
    apply bounds_mul hx192 hx234 <;> norm_num
  let x236 : ℝ := x192*x235
  have hx236 : Bounds (339322038137 / 1000000000000) (169677194919 / 500000000000) x236 := by
    apply bounds_mul hx192 hx235 <;> norm_num
  let x237 : ℝ := x192^3
  have hx237 : Bounds (339322038137 / 1000000000000) (169677194919 / 500000000000) x237 := by
    (convert hx236 using 1; ring)
  let x238 : ℝ := x233*x237
  have hx238 : Bounds (228257402509 / 500000000000) (456605059297 / 1000000000000) x238 := by
    apply bounds_mul hx233 hx237 <;> norm_num
  let x239 : ℝ := x238⁻¹
  have hx239 : Bounds (136879779861 / 62500000000) (2190509462143 / 1000000000000) x239 := by
    apply bounds_inv hx238 <;> norm_num
  let x240 : ℝ := x228*x239
  have hx240 : Bounds (1045618582537 / 500000000000) (83674029047 / 40000000000) x240 := by
    apply bounds_mul hx228 hx239 <;> norm_num
  let x241 : ℝ := x228/x238
  have hx241 : Bounds (1045618582537 / 500000000000) (83674029047 / 40000000000) x241 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx240
  let x242 : ℝ := -x209
  have hx242 : Bounds (-93491443 / 1000000000) (-93253379 / 1000000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x243 : ℝ := (2 / 1)*x192
  have hx243 : Bounds (1394977977 / 1000000000) (1395022309 / 1000000000) x243 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x244 : ℝ := c*(1 / 1)
  have hx244 : Bounds (11623 / 125000) (4661 / 50000) x244 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x245 : ℝ := c*x244
  have hx245 : Bounds (135094129 / 15625000000) (21724921 / 2500000000) x245 := by
    apply bounds_mul hc hx244 <;> norm_num
  let x246 : ℝ := c^2
  have hx246 : Bounds (135094129 / 15625000000) (21724921 / 2500000000) x246 := by
    (convert hx245 using 1; ring)
  let x247 : ℝ := -x246
  have hx247 : Bounds (-21724921 / 2500000000) (-135094129 / 15625000000) x247 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx246
  let x248 : ℝ := x243+x247
  have hx248 : Bounds (6931440043 / 5000000000) (173297035593 / 125000000000) x248 := by
    apply bounds_add hx243 hx247 <;> norm_num
  let x249 : ℝ := x243-x246
  have hx249 : Bounds (6931440043 / 5000000000) (173297035593 / 125000000000) x249 := by
    exact hx248
  let x250 : ℝ := x242*x249
  have hx250 : Bounds (-64807159701 / 500000000000) (-129276041069 / 1000000000000) x250 := by
    apply bounds_mul hx242 hx249 <;> norm_num
  let x251 : ℝ := x198⁻¹
  have hx251 : Bounds (20174428599 / 20000000000) (252191536483 / 250000000000) x251 := by
    apply bounds_inv hx198 <;> norm_num
  let x252 : ℝ := c*x251
  have hx252 : Bounds (46897476721 / 500000000000) (23509295031 / 250000000000) x252 := by
    apply bounds_mul hc hx251 <;> norm_num
  let x253 : ℝ := c/x198
  have hx253 : Bounds (46897476721 / 500000000000) (23509295031 / 250000000000) x253 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx252
  let x254 : ℝ := (2 / 1)*x253
  have hx254 : Bounds (46897476721 / 250000000000) (23509295031 / 125000000000) x254 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx253 <;> norm_num
  let x255 : ℝ := (2 / 1)*c
  have hx255 : Bounds (11623 / 62500) (4661 / 25000) x255 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hc <;> norm_num
  let x256 : ℝ := -x255
  have hx256 : Bounds (-4661 / 25000) (-11623 / 62500) x256 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx255
  let x257 : ℝ := x254+x256
  have hx257 : Bounds (287476721 / 250000000000) (263295031 / 125000000000) x257 := by
    apply bounds_add hx254 hx256 <;> norm_num
  let x258 : ℝ := x254-x255
  have hx258 : Bounds (287476721 / 250000000000) (263295031 / 125000000000) x258 := by
    exact hx257
  let x259 : ℝ := x180*x258
  have hx259 : Bounds (198012781 / 250000000000) (725449341 / 500000000000) x259 := by
    apply bounds_mul hx180 hx258 <;> norm_num
  let x260 : ℝ := x250+x259
  have hx260 : Bounds (-64411134139 / 500000000000) (-127825142387 / 1000000000000) x260 := by
    apply bounds_add hx250 hx259 <;> norm_num
  let x261 : ℝ := (2 / 1)*x90
  have hx261 : Bounds (42783254607 / 31250000000) (27381657771 / 20000000000) x261 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x262 : ℝ := x198*(1 / 1)
  have hx262 : Bounds (2478275079 / 2500000000) (15489905871 / 15625000000) x262 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x263 : ℝ := x198*x262
  have hx263 : Bounds (786156463 / 800000000) (122847838153 / 125000000000) x263 := by
    apply bounds_mul hx198 hx262 <;> norm_num
  let x264 : ℝ := x198^2
  have hx264 : Bounds (786156463 / 800000000) (122847838153 / 125000000000) x264 := by
    (convert hx263 using 1; ring)
  let x265 : ℝ := x261*x264
  have hx265 : Bounds (672686642349 / 500000000000) (672755492443 / 500000000000) x265 := by
    apply bounds_mul hx261 hx264 <;> norm_num
  let x266 : ℝ := x192*(1 / 1)
  have hx266 : Bounds (1394977977 / 2000000000) (1395022309 / 2000000000) x266 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x267 : ℝ := x192*x266
  have hx267 : Bounds (243245444539 / 500000000000) (121630452663 / 250000000000) x267 := by
    apply bounds_mul hx192 hx266 <;> norm_num
  let x268 : ℝ := x192*x267
  have hx268 : Bounds (339322038137 / 1000000000000) (169677194919 / 500000000000) x268 := by
    apply bounds_mul hx192 hx267 <;> norm_num
  let x269 : ℝ := x192^3
  have hx269 : Bounds (339322038137 / 1000000000000) (169677194919 / 500000000000) x269 := by
    (convert hx268 using 1; ring)
  let x270 : ℝ := x265*x269
  have hx270 : Bounds (228257402509 / 500000000000) (456605059297 / 1000000000000) x270 := by
    apply bounds_mul hx265 hx269 <;> norm_num
  let x271 : ℝ := x270⁻¹
  have hx271 : Bounds (136879779861 / 62500000000) (2190509462143 / 1000000000000) x271 := by
    apply bounds_inv hx270 <;> norm_num
  let x272 : ℝ := x260*x271
  have hx272 : Bounds (-141093198799 / 500000000000) (-27994683761 / 100000000000) x272 := by
    apply bounds_mul hx260 hx271 <;> norm_num
  let x273 : ℝ := x260/x270
  have hx273 : Bounds (-141093198799 / 500000000000) (-27994683761 / 100000000000) x273 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx272
  let x274 : ℝ := (4 / 1)*c
  have hx274 : Bounds (11623 / 31250) (4661 / 12500) x274 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hc <;> norm_num
  let x275 : ℝ := x198⁻¹
  have hx275 : Bounds (20174428599 / 20000000000) (252191536483 / 250000000000) x275 := by
    apply bounds_inv hx198 <;> norm_num
  let x276 : ℝ := x274*x275
  have hx276 : Bounds (375179813769 / 1000000000000) (23509295031 / 62500000000) x276 := by
    apply bounds_mul hx274 hx275 <;> norm_num
  let x277 : ℝ := x274/x198
  have hx277 : Bounds (375179813769 / 1000000000000) (23509295031 / 62500000000) x277 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx276
  let x278 : ℝ := (3 / 1)*c
  have hx278 : Bounds (34869 / 125000) (13983 / 50000) x278 := by
    apply bounds_mul (bounds_const ((3 / 1) : ℝ)) hc <;> norm_num
  let x279 : ℝ := x198*x192
  have hx279 : Bounds (69142783123 / 100000000000) (34574022807 / 50000000000) x279 := by
    apply bounds_mul hx198 hx192 <;> norm_num
  let x280 : ℝ := x279⁻¹
  have hx280 : Bounds (723086235569 / 500000000000) (1412385293 / 976562500) x280 := by
    apply bounds_inv hx279 <;> norm_num
  let x281 : ℝ := x278*x280
  have hx281 : Bounds (6303323487 / 15625000000) (202233687573 / 500000000000) x281 := by
    apply bounds_mul hx278 hx280 <;> norm_num
  let x282 : ℝ := x278/x279
  have hx282 : Bounds (6303323487 / 15625000000) (202233687573 / 500000000000) x282 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx281
  let x283 : ℝ := -x282
  have hx283 : Bounds (-202233687573 / 500000000000) (-6303323487 / 15625000000) x283 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx282
  let x284 : ℝ := x277+x283
  have hx284 : Bounds (-29287561377 / 1000000000000) (-1703998917 / 62500000000) x284 := by
    apply bounds_add hx277 hx283 <;> norm_num
  let x285 : ℝ := x277-x282
  have hx285 : Bounds (-29287561377 / 1000000000000) (-1703998917 / 62500000000) x285 := by
    exact hx284
  let x286 : ℝ := x241*x285
  have hx286 : Bounds (-12253041307 / 200000000000) (-57015453831 / 1000000000000) x286 := by
    apply bounds_mul hx241 hx285 <;> norm_num
  let x287 : ℝ := x273+x286
  have hx287 : Bounds (-343451604133 / 1000000000000) (-336962291441 / 1000000000000) x287 := by
    apply bounds_add hx273 hx286 <;> norm_num
  let x288 : ℝ := (2 / 1)*x192
  have hx288 : Bounds (1394977977 / 1000000000) (1395022309 / 1000000000) x288 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x289 : ℝ := c*(1 / 1)
  have hx289 : Bounds (11623 / 125000) (4661 / 50000) x289 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x290 : ℝ := c*x289
  have hx290 : Bounds (135094129 / 15625000000) (21724921 / 2500000000) x290 := by
    apply bounds_mul hc hx289 <;> norm_num
  let x291 : ℝ := c^2
  have hx291 : Bounds (135094129 / 15625000000) (21724921 / 2500000000) x291 := by
    (convert hx290 using 1; ring)
  let x292 : ℝ := -x291
  have hx292 : Bounds (-21724921 / 2500000000) (-135094129 / 15625000000) x292 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx291
  let x293 : ℝ := x288+x292
  have hx293 : Bounds (6931440043 / 5000000000) (173297035593 / 125000000000) x293 := by
    apply bounds_add hx288 hx292 <;> norm_num
  let x294 : ℝ := x288-x291
  have hx294 : Bounds (6931440043 / 5000000000) (173297035593 / 125000000000) x294 := by
    exact hx293
  let x295 : ℝ := c*x294
  have hx295 : Bounds (128902604191 / 1000000000000) (8077374829 / 62500000000) x295 := by
    apply bounds_mul hc hx294 <;> norm_num
  let x296 : ℝ := x198*(1 / 1)
  have hx296 : Bounds (2478275079 / 2500000000) (15489905871 / 15625000000) x296 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x297 : ℝ := x198*x296
  have hx297 : Bounds (786156463 / 800000000) (122847838153 / 125000000000) x297 := by
    apply bounds_mul hx198 hx296 <;> norm_num
  let x298 : ℝ := x198^2
  have hx298 : Bounds (786156463 / 800000000) (122847838153 / 125000000000) x298 := by
    (convert hx297 using 1; ring)
  let x299 : ℝ := x192*(1 / 1)
  have hx299 : Bounds (1394977977 / 2000000000) (1395022309 / 2000000000) x299 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x300 : ℝ := x192*x299
  have hx300 : Bounds (243245444539 / 500000000000) (121630452663 / 250000000000) x300 := by
    apply bounds_mul hx192 hx299 <;> norm_num
  let x301 : ℝ := x192^2
  have hx301 : Bounds (243245444539 / 500000000000) (121630452663 / 250000000000) x301 := by
    (convert hx300 using 1; ring)
  let x302 : ℝ := x298*x301
  have hx302 : Bounds (478072445799 / 1000000000000) (59768152653 / 125000000000) x302 := by
    apply bounds_mul hx298 hx301 <;> norm_num
  let x303 : ℝ := x302⁻¹
  have hx303 : Bounds (2091414816277 / 1000000000000) (2091733185603 / 1000000000000) x303 := by
    apply bounds_inv hx302 <;> norm_num
  let x304 : ℝ := x295*x303
  have hx304 : Bounds (269588816261 / 1000000000000) (135165703859 / 500000000000) x304 := by
    apply bounds_mul hx295 hx303 <;> norm_num
  let x305 : ℝ := x295/x302
  have hx305 : Bounds (269588816261 / 1000000000000) (135165703859 / 500000000000) x305 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx304
  let x306 : ℝ := c*x220
  have hx306 : Bounds (1740241773 / 100000000000) (8728119431 / 500000000000) x306 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x307 : ℝ := x180+x306
  have hx307 : Bounds (706198298413 / 1000000000000) (176568539281 / 250000000000) x307 := by
    apply bounds_add hx180 hx306 <;> norm_num
  let x308 : ℝ := x307*(1 / 1)
  have hx308 : Bounds (706198298413 / 1000000000000) (176568539281 / 250000000000) x308 := by
    apply bounds_mul hx307 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x309 : ℝ := x307*x308
  have hx309 : Bounds (498716036681 / 1000000000000) (249411592511 / 500000000000) x309 := by
    apply bounds_mul hx307 hx308 <;> norm_num
  let x310 : ℝ := x307^2
  have hx310 : Bounds (498716036681 / 1000000000000) (249411592511 / 500000000000) x310 := by
    (convert hx309 using 1; ring)
  let x311 : ℝ := x287*x310
  have hx311 : Bounds (-6852864923 / 40000000000) (-84024249249 / 500000000000) x311 := by
    apply bounds_mul hx287 hx310 <;> norm_num
  let x312 : ℝ := (2 / 1)*x241
  have hx312 : Bounds (1045618582537 / 250000000000) (83674029047 / 20000000000) x312 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx241 <;> norm_num
  let x313 : ℝ := c*x220
  have hx313 : Bounds (1740241773 / 100000000000) (8728119431 / 500000000000) x313 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x314 : ℝ := x180+x313
  have hx314 : Bounds (706198298413 / 1000000000000) (176568539281 / 250000000000) x314 := by
    apply bounds_add hx180 hx313 <;> norm_num
  let x315 : ℝ := x312*x314
  have hx315 : Bounds (1476828127553 / 500000000000) (2954840216917 / 1000000000000) x315 := by
    apply bounds_mul hx312 hx314 <;> norm_num
  let x316 : ℝ := -x209
  have hx316 : Bounds (-93491443 / 1000000000) (-93253379 / 1000000000) x316 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x317 : ℝ := x220+x316
  have hx317 : Bounds (93663527 / 1000000000) (94005137 / 1000000000) x317 := by
    apply bounds_add hx220 hx316 <;> norm_num
  let x318 : ℝ := x220-x209
  have hx318 : Bounds (93663527 / 1000000000) (94005137 / 1000000000) x318 := by
    exact hx317
  let x319 : ℝ := x315*x318
  have hx319 : Bounds (138324931199 / 500000000000) (55554031881 / 200000000000) x319 := by
    apply bounds_mul hx315 hx318 <;> norm_num
  let x320 : ℝ := x311+x319
  have hx320 : Bounds (105328239323 / 1000000000000) (109721660907 / 1000000000000) x320 := by
    apply bounds_add hx311 hx319 <;> norm_num
  let x321 : ℝ := a*(1 / 1)
  have hx321 : Bounds (37 / 200) (1851 / 10000) x321 := by
    apply bounds_mul ha (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x322 : ℝ := a*x321
  have hx322 : Bounds (1369 / 40000) (3426201 / 100000000) x322 := by
    apply bounds_mul ha hx321 <;> norm_num
  let x323 : ℝ := a^2
  have hx323 : Bounds (1369 / 40000) (3426201 / 100000000) x323 := by
    (convert hx322 using 1; ring)
  let x324 : ℝ := -x323
  have hx324 : Bounds (-3426201 / 100000000) (-1369 / 40000) x324 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx323
  let x325 : ℝ := (1 / 1)+x324
  have hx325 : Bounds (96573799 / 100000000) (38631 / 40000) x325 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx324 <;> norm_num
  let x326 : ℝ := (1 / 1)-x323
  have hx326 : Bounds (96573799 / 100000000) (38631 / 40000) x326 := by
    exact hx325
  let x327 : ℝ := x326⁻¹
  have hx327 : Bounds (207087572157 / 200000000000) (129434692737 / 125000000000) x327 := by
    apply bounds_inv hx326 <;> norm_num
  let x328 : ℝ := (1 / 1)*x327
  have hx328 : Bounds (207087572157 / 200000000000) (129434692737 / 125000000000) x328 := by
    apply bounds_mul (bounds_const ((1 / 1) : ℝ)) hx327 <;> norm_num
  let x329 : ℝ := (1 / 1)/x326
  have hx329 : Bounds (207087572157 / 200000000000) (129434692737 / 125000000000) x329 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx328
  let x330 : ℝ := x329*x305
  have hx330 : Bounds (87232021 / 312500000) (139961050781 / 500000000000) x330 := by
    apply bounds_mul hx329 hx305 <;> norm_num
  let x331 : ℝ := x320+x330
  have hx331 : Bounds (384470706523 / 1000000000000) (389643762469 / 1000000000000) x331 := by
    apply bounds_add hx320 hx330 <;> norm_num
  let x332 : ℝ := x180*(1 / 1)
  have hx332 : Bounds (688795880683 / 1000000000000) (344408959131 / 500000000000) x332 := by
    apply bounds_mul hx180 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x333 : ℝ := x180*x332
  have hx333 : Bounds (94887953049 / 200000000000) (474470124519 / 1000000000000) x333 := by
    apply bounds_mul hx180 hx332 <;> norm_num
  let x334 : ℝ := x180^2
  have hx334 : Bounds (94887953049 / 200000000000) (474470124519 / 1000000000000) x334 := by
    (convert hx333 using 1; ring)
  let x335 : ℝ := x331*x334
  have hx335 : Bounds (91204095873 / 500000000000) (184874324497 / 1000000000000) x335 := by
    apply bounds_mul hx331 hx334 <;> norm_num
  let x336 : ℝ := x90*x192
  have hx336 : Bounds (477453583689 / 1000000000000) (4774752931 / 10000000000) x336 := by
    apply bounds_mul hx90 hx192 <;> norm_num
  let x337 : ℝ := x336⁻¹
  have hx337 : Bounds (2094349203929 / 1000000000000) (2094444432219 / 1000000000000) x337 := by
    apply bounds_inv hx336 <;> norm_num
  let x338 : ℝ := x335*x337
  have hx338 : Bounds (382026451173 / 1000000000000) (387208999603 / 1000000000000) x338 := by
    apply bounds_mul hx335 hx337 <;> norm_num
  let x339 : ℝ := x335/x336
  have hx339 : Bounds (382026451173 / 1000000000000) (387208999603 / 1000000000000) x339 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx338
  have hu : x339 < (1169852961734184398083 / 2984708322000000000000) := lt_of_le_of_lt hx339.2 (by norm_num)
  simpa +zetaDelta only [ScFormula,Kprime,K,Mprime,SmallMean.A,biasB,div_one,pow_two] using hu

open GeneralCK.Reflection
/-- Uniform derivative enclosure including input boxes with z=0. -/
theorem derivative_bound_350 {a z s : ℝ}
    (ha : a ∈ Set.Icc ((37 / 200):ℝ) ((1851 / 10000)))
    (hz : z ∈ Set.Icc (0:ℝ) (1/1000))
    (hs : s ∈ Set.Ioo (a*(1-z)/2) (a*(1+z)/2)) :
    P a ((biasE a+biasE (a*z))/2) s ≤ (1169852961734184398083 / 2984708322000000000000) := by
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
  have hsl : (36963 / 400000) ≤ s := by
    have h := mul_le_mul ha.1 (show (999/1000:ℝ) ≤ 1-z by linarith [hz.2])
      (by norm_num : (0:ℝ) ≤ 999/1000) ha0.le
    nlinarith [hs.1]
  have hsu : s ≤ (1852851 / 20000000) := by
    have h := mul_le_mul ha.2 (show 1+z ≤ (1001/1000:ℝ) by linarith [hz.2])
      (by linarith [hz.1] : 0 ≤ 1+z) (by norm_num : (0:ℝ) ≤ (1851 / 10000))
    nlinarith [hs.2]
  have hy := div_pos he hs0
  have hc := biasContact_mem hy
  have heq : biasE (biasContact (((biasE a+biasE (a*z))/2)/s)) =
      (((biasE a+biasE (a*z))/2)/s)*biasContact (((biasE a+biasE (a*z))/2)/s) := by
    exact (div_eq_iff hc.1.ne').mp (biasR_biasContact hy)
  have hb := derivative_leaf_350 a z s _ ha hz ⟨hsl,hsu⟩ hc.1.le hc.2.le heq
  rw [P_eq_formula ha0 ha1 he hs0]
  exact hb.le

/-- Checked low-ratio strip: includes arbitrarily small positive z. -/
theorem curvature_leaf_350 {a z : ℝ}
    (ha : a ∈ Set.Icc ((37 / 200):ℝ) ((1851 / 10000)))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < curvature a (a*z) := by
  have ha0 : 0 < a := by linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  apply curvature_pos_of_derivative_bound ha0 ha1 hz.1 (by linarith [hz.2])
    (fun s hs => derivative_bound_350 ha ⟨hz.1.le,hz.2⟩ hs) (M := (1169852961734184398083 / 2984708322000000000000))
  exact lt_of_lt_of_le (by norm_num : (1169852961734184398083 / 2984708322000000000000) < 2*((37 / 200):ℝ)/(1-((37 / 200):ℝ)^2)^2)
    (base_mono (by norm_num) ha.1 ha1)

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Cell0351 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
theorem derivative_leaf_351 (a z s c : ℝ)
    (ha : Bounds (1851 / 10000) (463 / 2500) a) (hz : Bounds 0 (1/1000) z)
    (hs : Bounds (1849149 / 20000000) (463463 / 5000000) s) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (heq : biasE c = (((biasE a+biasE (a*z))/2)/s)*c) :
    ScFormula c a ((biasE a+biasE (a*z))/2)*(biasE c)^2 /
      (((biasE a+biasE (a*z))/2)*biasB c) < (3657698358973465937451856811 / 9326498653292401000000000000) := by
  let x0 : ℝ := Real.log (2 / 1)
  have hx0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x0 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x1 : ℝ := (1 / 1)+(463 / 2500)
  have hx1 : Bounds (2963 / 2500) (2963 / 2500) x1 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((463 / 2500) : ℝ)) <;> norm_num
  let x2 : ℝ := (1 / 1)+(463 / 2500)
  have hx2 : Bounds (2963 / 2500) (2963 / 2500) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((463 / 2500) : ℝ)) <;> norm_num
  let x3 : ℝ := Real.log x2
  have hx3 : Bounds (10619471 / 62500000) (169911537 / 1000000000) x3 := by
    exact bounds_log hx2 (by norm_num) (by simpa only [div_one] using reflection_log_4884.1) (by simpa only [div_one] using reflection_log_4884.2)
  let x4 : ℝ := x1*x3
  have hx4 : Bounds (201379152467 / 1000000000000) (201379153653 / 1000000000000) x4 := by
    apply bounds_mul hx1 hx3 <;> norm_num
  let x5 : ℝ := -(463 / 2500)
  have hx5 : Bounds (-463 / 2500) (-463 / 2500) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((463 / 2500) : ℝ))
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (2037 / 2500) (2037 / 2500) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-(463 / 2500)
  have hx7 : Bounds (2037 / 2500) (2037 / 2500) x7 := by
    exact hx6
  let x8 : ℝ := -(463 / 2500)
  have hx8 : Bounds (-463 / 2500) (-463 / 2500) x8 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((463 / 2500) : ℝ))
  let x9 : ℝ := (1 / 1)+x8
  have hx9 : Bounds (2037 / 2500) (2037 / 2500) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx8 <;> norm_num
  let x10 : ℝ := (1 / 1)-(463 / 2500)
  have hx10 : Bounds (2037 / 2500) (2037 / 2500) x10 := by
    exact hx9
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (-40962519 / 200000000) (-102406297 / 500000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_4885.1) (by simpa only [div_one] using reflection_log_4885.2)
  let x12 : ℝ := x7*x11
  have hx12 : Bounds (-83440651203 / 500000000000) (-166881301591 / 1000000000000) x12 := by
    apply bounds_mul hx7 hx11 <;> norm_num
  let x13 : ℝ := x4+x12
  have hx13 : Bounds (34497850061 / 1000000000000) (17248926031 / 500000000000) x13 := by
    apply bounds_add hx4 hx12 <;> norm_num
  let x14 : ℝ := (2 / 1)⁻¹
  have hx14 : Bounds (1 / 2) (1 / 2) x14 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x15 : ℝ := x13*x14
  have hx15 : Bounds (1724892503 / 100000000000) (17248926031 / 1000000000000) x15 := by
    apply bounds_mul hx13 hx14 <;> norm_num
  let x16 : ℝ := x13/(2 / 1)
  have hx16 : Bounds (1724892503 / 100000000000) (17248926031 / 1000000000000) x16 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx15
  let x17 : ℝ := -x16
  have hx17 : Bounds (-17248926031 / 1000000000000) (-1724892503 / 100000000000) x17 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx16
  let x18 : ℝ := x0+x17
  have hx18 : Bounds (675898253969 / 1000000000000) (67589825597 / 100000000000) x18 := by
    apply bounds_add hx0 hx17 <;> norm_num
  let x19 : ℝ := x0-x16
  have hx19 : Bounds (675898253969 / 1000000000000) (67589825597 / 100000000000) x19 := by
    exact hx18
  let x20 : ℝ := biasE (463 / 2500)
  have hx20 : Bounds (675898253969 / 1000000000000) (67589825597 / 100000000000) x20 := by
    simpa +zetaDelta only [biasE, div_one] using hx19
  let x21 : ℝ := Real.log (2 / 1)
  have hx21 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x21 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x22 : ℝ := (1 / 1)+(1851 / 10000)
  have hx22 : Bounds (11851 / 10000) (11851 / 10000) x22 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1851 / 10000) : ℝ)) <;> norm_num
  let x23 : ℝ := (1 / 1)+(1851 / 10000)
  have hx23 : Bounds (11851 / 10000) (11851 / 10000) x23 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1851 / 10000) : ℝ)) <;> norm_num
  let x24 : ℝ := Real.log x23
  have hx24 : Bounds (169827159 / 1000000000) (4245679 / 25000000) x24 := by
    exact bounds_log hx23 (by norm_num) (by simpa only [div_one] using reflection_log_4870.1) (by simpa only [div_one] using reflection_log_4870.2)
  let x25 : ℝ := x22*x24
  have hx25 : Bounds (20126216613 / 100000000000) (50315541829 / 250000000000) x25 := by
    apply bounds_mul hx22 hx24 <;> norm_num
  let x26 : ℝ := -(1851 / 10000)
  have hx26 : Bounds (-1851 / 10000) (-1851 / 10000) x26 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1851 / 10000) : ℝ))
  let x27 : ℝ := (1 / 1)+x26
  have hx27 : Bounds (8149 / 10000) (8149 / 10000) x27 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx26 <;> norm_num
  let x28 : ℝ := (1 / 1)-(1851 / 10000)
  have hx28 : Bounds (8149 / 10000) (8149 / 10000) x28 := by
    exact hx27
  let x29 : ℝ := -(1851 / 10000)
  have hx29 : Bounds (-1851 / 10000) (-1851 / 10000) x29 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1851 / 10000) : ℝ))
  let x30 : ℝ := (1 / 1)+x29
  have hx30 : Bounds (8149 / 10000) (8149 / 10000) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx29 <;> norm_num
  let x31 : ℝ := (1 / 1)-(1851 / 10000)
  have hx31 : Bounds (8149 / 10000) (8149 / 10000) x31 := by
    exact hx30
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (-204689873 / 1000000000) (-12793117 / 62500000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_4871.1) (by simpa only [div_one] using reflection_log_4871.2)
  let x33 : ℝ := x28*x32
  have hx33 : Bounds (-41700444377 / 250000000000) (-41700444173 / 250000000000) x33 := by
    apply bounds_mul hx28 hx32 <;> norm_num
  let x34 : ℝ := x25+x33
  have hx34 : Bounds (17230194311 / 500000000000) (1076887207 / 31250000000) x34 := by
    apply bounds_add hx25 hx33 <;> norm_num
  let x35 : ℝ := (2 / 1)⁻¹
  have hx35 : Bounds (1 / 2) (1 / 2) x35 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x36 : ℝ := x34*x35
  have hx36 : Bounds (17230194311 / 1000000000000) (1076887207 / 62500000000) x36 := by
    apply bounds_mul hx34 hx35 <;> norm_num
  let x37 : ℝ := x34/(2 / 1)
  have hx37 : Bounds (17230194311 / 1000000000000) (1076887207 / 62500000000) x37 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx36
  let x38 : ℝ := -x37
  have hx38 : Bounds (-1076887207 / 62500000000) (-17230194311 / 1000000000000) x38 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx37
  let x39 : ℝ := x21+x38
  have hx39 : Bounds (42244811543 / 62500000000) (675916986689 / 1000000000000) x39 := by
    apply bounds_add hx21 hx38 <;> norm_num
  let x40 : ℝ := x21-x37
  have hx40 : Bounds (42244811543 / 62500000000) (675916986689 / 1000000000000) x40 := by
    exact hx39
  let x41 : ℝ := biasE (1851 / 10000)
  have hx41 : Bounds (42244811543 / 62500000000) (675916986689 / 1000000000000) x41 := by
    simpa +zetaDelta only [biasE, div_one] using hx40
  let x42 : ℝ := biasE a
  have hx42 : Bounds (675898253969 / 1000000000000) (675916986689 / 1000000000000) x42 := by
    exact bounds_biasE ha (by norm_num) (by norm_num) hx20.1 hx41.2
  let x43 : ℝ := a*z
  have hx43 : Bounds (0 / 1) (463 / 2500000) x43 := by
    apply bounds_mul ha hz <;> norm_num
  let x44 : ℝ := Real.log (2 / 1)
  have hx44 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x44 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x45 : ℝ := (1 / 1)+(463 / 2500000)
  have hx45 : Bounds (2500463 / 2500000) (2500463 / 2500000) x45 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((463 / 2500000) : ℝ)) <;> norm_num
  let x46 : ℝ := (1 / 1)+(463 / 2500000)
  have hx46 : Bounds (2500463 / 2500000) (2500463 / 2500000) x46 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((463 / 2500000) : ℝ)) <;> norm_num
  let x47 : ℝ := Real.log x46
  have hx47 : Bounds (92591 / 500000000) (185183 / 1000000000) x47 := by
    exact bounds_log hx46 (by norm_num) (by simpa only [div_one] using reflection_log_4886.1) (by simpa only [div_one] using reflection_log_4886.2)
  let x48 : ℝ := x45*x47
  have hx48 : Bounds (37043259 / 200000000000) (11576081 / 62500000000) x48 := by
    apply bounds_mul hx45 hx47 <;> norm_num
  let x49 : ℝ := -(463 / 2500000)
  have hx49 : Bounds (-463 / 2500000) (-463 / 2500000) x49 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((463 / 2500000) : ℝ))
  let x50 : ℝ := (1 / 1)+x49
  have hx50 : Bounds (2499537 / 2500000) (2499537 / 2500000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx49 <;> norm_num
  let x51 : ℝ := (1 / 1)-(463 / 2500000)
  have hx51 : Bounds (2499537 / 2500000) (2499537 / 2500000) x51 := by
    exact hx50
  let x52 : ℝ := -(463 / 2500000)
  have hx52 : Bounds (-463 / 2500000) (-463 / 2500000) x52 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((463 / 2500000) : ℝ))
  let x53 : ℝ := (1 / 1)+x52
  have hx53 : Bounds (2499537 / 2500000) (2499537 / 2500000) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx52 <;> norm_num
  let x54 : ℝ := (1 / 1)-(463 / 2500000)
  have hx54 : Bounds (2499537 / 2500000) (2499537 / 2500000) x54 := by
    exact hx53
  let x55 : ℝ := Real.log x54
  have hx55 : Bounds (-92609 / 500000000) (-185217 / 1000000000) x55 := by
    exact bounds_log hx54 (by norm_num) (by simpa only [div_one] using reflection_log_4887.1) (by simpa only [div_one] using reflection_log_4887.2)
  let x56 : ℝ := x51*x55
  have hx56 : Bounds (-92591849 / 500000000000) (-185182697 / 1000000000000) x56 := by
    apply bounds_mul hx51 hx55 <;> norm_num
  let x57 : ℝ := x48+x56
  have hx57 : Bounds (32597 / 1000000000000) (34599 / 1000000000000) x57 := by
    apply bounds_add hx48 hx56 <;> norm_num
  let x58 : ℝ := (2 / 1)⁻¹
  have hx58 : Bounds (1 / 2) (1 / 2) x58 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x59 : ℝ := x57*x58
  have hx59 : Bounds (8149 / 500000000000) (173 / 10000000000) x59 := by
    apply bounds_mul hx57 hx58 <;> norm_num
  let x60 : ℝ := x57/(2 / 1)
  have hx60 : Bounds (8149 / 500000000000) (173 / 10000000000) x60 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx59
  let x61 : ℝ := -x60
  have hx61 : Bounds (-173 / 10000000000) (-8149 / 500000000000) x61 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx60
  let x62 : ℝ := x44+x61
  have hx62 : Bounds (6931471627 / 10000000000) (346573582351 / 500000000000) x62 := by
    apply bounds_add hx44 hx61 <;> norm_num
  let x63 : ℝ := x44-x60
  have hx63 : Bounds (6931471627 / 10000000000) (346573582351 / 500000000000) x63 := by
    exact hx62
  let x64 : ℝ := biasE (463 / 2500000)
  have hx64 : Bounds (6931471627 / 10000000000) (346573582351 / 500000000000) x64 := by
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
  have hx86 : Bounds (6931471627 / 10000000000) (693147181 / 1000000000) x86 := by
    exact bounds_biasE hx43 (by norm_num) (by norm_num) hx64.1 hx85.2
  let x87 : ℝ := x42+x86
  have hx87 : Bounds (1369045416669 / 1000000000000) (1369064167689 / 1000000000000) x87 := by
    apply bounds_add hx42 hx86 <;> norm_num
  let x88 : ℝ := (2 / 1)⁻¹
  have hx88 : Bounds (1 / 2) (1 / 2) x88 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x89 : ℝ := x87*x88
  have hx89 : Bounds (342261354167 / 500000000000) (136906416769 / 200000000000) x89 := by
    apply bounds_mul hx87 hx88 <;> norm_num
  let x90 : ℝ := x87/(2 / 1)
  have hx90 : Bounds (342261354167 / 500000000000) (136906416769 / 200000000000) x90 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx89
  let x91 : ℝ := s⁻¹
  have hx91 : Bounds (10788347721393 / 1000000000000) (2163157214481 / 200000000000) x91 := by
    apply bounds_inv hs <;> norm_num
  let x92 : ℝ := x90*x91
  have hx92 : Bounds (923108625087 / 125000000000) (3701876289283 / 500000000000) x92 := by
    apply bounds_mul hx90 hx91 <;> norm_num
  let x93 : ℝ := x90/s
  have hx93 : Bounds (923108625087 / 125000000000) (3701876289283 / 500000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(18607 / 200000)
  have hx95 : Bounds (218607 / 200000) (218607 / 200000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((18607 / 200000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(18607 / 200000)
  have hx96 : Bounds (218607 / 200000) (218607 / 200000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((18607 / 200000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (8895823 / 100000000) (88958231 / 1000000000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_4888.1) (by simpa only [div_one] using reflection_log_4888.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (6077153683 / 62500000000) (48617230011 / 500000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(18607 / 200000)
  have hx99 : Bounds (-18607 / 200000) (-18607 / 200000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((18607 / 200000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (181393 / 200000) (181393 / 200000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(18607 / 200000)
  have hx101 : Bounds (181393 / 200000) (181393 / 200000) x101 := by
    exact hx100
  let x102 : ℝ := -(18607 / 200000)
  have hx102 : Bounds (-18607 / 200000) (-18607 / 200000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((18607 / 200000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (181393 / 200000) (181393 / 200000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(18607 / 200000)
  have hx104 : Bounds (181393 / 200000) (181393 / 200000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-97651419 / 1000000000) (-48825709 / 500000000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_4889.1) (by simpa only [div_one] using reflection_log_4889.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-44283209617 / 500000000000) (-44283209163 / 500000000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (4334019847 / 500000000000) (270876303 / 31250000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (4334019847 / 1000000000000) (270876303 / 62500000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (4334019847 / 1000000000000) (270876303 / 62500000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-270876303 / 62500000000) (-4334019847 / 1000000000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (43050822447 / 62500000000) (688813161153 / 1000000000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (43050822447 / 62500000000) (688813161153 / 1000000000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (18607 / 200000)
  have hx114 : Bounds (43050822447 / 62500000000) (688813161153 / 1000000000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(93271 / 1000000)
  have hx116 : Bounds (1093271 / 1000000) (1093271 / 1000000) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((93271 / 1000000) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(93271 / 1000000)
  have hx117 : Bounds (1093271 / 1000000) (1093271 / 1000000) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((93271 / 1000000) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (89174119 / 1000000000) (2229353 / 25000000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_4890.1) (by simpa only [div_one] using reflection_log_4890.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (97491478253 / 1000000000000) (97491479347 / 1000000000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(93271 / 1000000)
  have hx120 : Bounds (-93271 / 1000000) (-93271 / 1000000) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((93271 / 1000000) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (906729 / 1000000) (906729 / 1000000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(93271 / 1000000)
  have hx122 : Bounds (906729 / 1000000) (906729 / 1000000) x122 := by
    exact hx121
  let x123 : ℝ := -(93271 / 1000000)
  have hx123 : Bounds (-93271 / 1000000) (-93271 / 1000000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((93271 / 1000000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (906729 / 1000000) (906729 / 1000000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(93271 / 1000000)
  have hx125 : Bounds (906729 / 1000000) (906729 / 1000000) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-97911661 / 1000000000) (-4895583 / 50000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_4891.1) (by simpa only [div_one] using reflection_log_4891.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-88779342467 / 1000000000000) (-2219483539 / 25000000000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (4356067893 / 500000000000) (8712137787 / 1000000000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (4356067893 / 1000000000000) (2178034447 / 500000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (4356067893 / 1000000000000) (2178034447 / 500000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-2178034447 / 500000000000) (-4356067893 / 1000000000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (344395555553 / 500000000000) (688791113107 / 1000000000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (344395555553 / 500000000000) (688791113107 / 1000000000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (93271 / 1000000)
  have hx135 : Bounds (344395555553 / 500000000000) (688791113107 / 1000000000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(18607 / 200000)
  have hx136 : Bounds (687051287479 / 1000000000000) (688808121147 / 1000000000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((18607 / 200000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(93271 / 1000000)
  have hx137 : Bounds (688794116563 / 1000000000000) (172638851689 / 250000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((93271 / 1000000) : ℝ)) <;> norm_num
  have hc : Bounds (18607 / 200000) (93271 / 1000000) c := by
    apply contact_bracket hc0 hc1 (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x93 by linarith [hx93.1])
      (show biasE c = x93*c by simpa +zetaDelta only [div_one] using heq)
    · have h1 : x93*(18607 / 200000) ≤ (688808121147 / 1000000000000) := hx136.2
      have h2 : (43050822447 / 62500000000) ≤ biasE (18607 / 200000) := hx114.1
      linarith
    · have h1 : biasE (93271 / 1000000) ≤ (688791113107 / 1000000000000) := hx135.2
      have h2 : (688794116563 / 1000000000000) ≤ x93*(93271 / 1000000) := hx137.1
      linarith
  let x138 : ℝ := Real.log (2 / 1)
  have hx138 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x138 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x139 : ℝ := (1 / 1)+(93271 / 1000000)
  have hx139 : Bounds (1093271 / 1000000) (1093271 / 1000000) x139 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((93271 / 1000000) : ℝ)) <;> norm_num
  let x140 : ℝ := (1 / 1)+(93271 / 1000000)
  have hx140 : Bounds (1093271 / 1000000) (1093271 / 1000000) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((93271 / 1000000) : ℝ)) <;> norm_num
  let x141 : ℝ := Real.log x140
  have hx141 : Bounds (89174119 / 1000000000) (2229353 / 25000000) x141 := by
    exact bounds_log hx140 (by norm_num) (by simpa only [div_one] using reflection_log_4890.1) (by simpa only [div_one] using reflection_log_4890.2)
  let x142 : ℝ := x139*x141
  have hx142 : Bounds (97491478253 / 1000000000000) (97491479347 / 1000000000000) x142 := by
    apply bounds_mul hx139 hx141 <;> norm_num
  let x143 : ℝ := -(93271 / 1000000)
  have hx143 : Bounds (-93271 / 1000000) (-93271 / 1000000) x143 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((93271 / 1000000) : ℝ))
  let x144 : ℝ := (1 / 1)+x143
  have hx144 : Bounds (906729 / 1000000) (906729 / 1000000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx143 <;> norm_num
  let x145 : ℝ := (1 / 1)-(93271 / 1000000)
  have hx145 : Bounds (906729 / 1000000) (906729 / 1000000) x145 := by
    exact hx144
  let x146 : ℝ := -(93271 / 1000000)
  have hx146 : Bounds (-93271 / 1000000) (-93271 / 1000000) x146 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((93271 / 1000000) : ℝ))
  let x147 : ℝ := (1 / 1)+x146
  have hx147 : Bounds (906729 / 1000000) (906729 / 1000000) x147 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx146 <;> norm_num
  let x148 : ℝ := (1 / 1)-(93271 / 1000000)
  have hx148 : Bounds (906729 / 1000000) (906729 / 1000000) x148 := by
    exact hx147
  let x149 : ℝ := Real.log x148
  have hx149 : Bounds (-97911661 / 1000000000) (-4895583 / 50000000) x149 := by
    exact bounds_log hx148 (by norm_num) (by simpa only [div_one] using reflection_log_4891.1) (by simpa only [div_one] using reflection_log_4891.2)
  let x150 : ℝ := x145*x149
  have hx150 : Bounds (-88779342467 / 1000000000000) (-2219483539 / 25000000000) x150 := by
    apply bounds_mul hx145 hx149 <;> norm_num
  let x151 : ℝ := x142+x150
  have hx151 : Bounds (4356067893 / 500000000000) (8712137787 / 1000000000000) x151 := by
    apply bounds_add hx142 hx150 <;> norm_num
  let x152 : ℝ := (2 / 1)⁻¹
  have hx152 : Bounds (1 / 2) (1 / 2) x152 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x153 : ℝ := x151*x152
  have hx153 : Bounds (4356067893 / 1000000000000) (2178034447 / 500000000000) x153 := by
    apply bounds_mul hx151 hx152 <;> norm_num
  let x154 : ℝ := x151/(2 / 1)
  have hx154 : Bounds (4356067893 / 1000000000000) (2178034447 / 500000000000) x154 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx153
  let x155 : ℝ := -x154
  have hx155 : Bounds (-2178034447 / 500000000000) (-4356067893 / 1000000000000) x155 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx154
  let x156 : ℝ := x138+x155
  have hx156 : Bounds (344395555553 / 500000000000) (688791113107 / 1000000000000) x156 := by
    apply bounds_add hx138 hx155 <;> norm_num
  let x157 : ℝ := x138-x154
  have hx157 : Bounds (344395555553 / 500000000000) (688791113107 / 1000000000000) x157 := by
    exact hx156
  let x158 : ℝ := biasE (93271 / 1000000)
  have hx158 : Bounds (344395555553 / 500000000000) (688791113107 / 1000000000000) x158 := by
    simpa +zetaDelta only [biasE, div_one] using hx157
  let x159 : ℝ := Real.log (2 / 1)
  have hx159 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x159 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x160 : ℝ := (1 / 1)+(18607 / 200000)
  have hx160 : Bounds (218607 / 200000) (218607 / 200000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((18607 / 200000) : ℝ)) <;> norm_num
  let x161 : ℝ := (1 / 1)+(18607 / 200000)
  have hx161 : Bounds (218607 / 200000) (218607 / 200000) x161 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((18607 / 200000) : ℝ)) <;> norm_num
  let x162 : ℝ := Real.log x161
  have hx162 : Bounds (8895823 / 100000000) (88958231 / 1000000000) x162 := by
    exact bounds_log hx161 (by norm_num) (by simpa only [div_one] using reflection_log_4888.1) (by simpa only [div_one] using reflection_log_4888.2)
  let x163 : ℝ := x160*x162
  have hx163 : Bounds (6077153683 / 62500000000) (48617230011 / 500000000000) x163 := by
    apply bounds_mul hx160 hx162 <;> norm_num
  let x164 : ℝ := -(18607 / 200000)
  have hx164 : Bounds (-18607 / 200000) (-18607 / 200000) x164 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((18607 / 200000) : ℝ))
  let x165 : ℝ := (1 / 1)+x164
  have hx165 : Bounds (181393 / 200000) (181393 / 200000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx164 <;> norm_num
  let x166 : ℝ := (1 / 1)-(18607 / 200000)
  have hx166 : Bounds (181393 / 200000) (181393 / 200000) x166 := by
    exact hx165
  let x167 : ℝ := -(18607 / 200000)
  have hx167 : Bounds (-18607 / 200000) (-18607 / 200000) x167 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((18607 / 200000) : ℝ))
  let x168 : ℝ := (1 / 1)+x167
  have hx168 : Bounds (181393 / 200000) (181393 / 200000) x168 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx167 <;> norm_num
  let x169 : ℝ := (1 / 1)-(18607 / 200000)
  have hx169 : Bounds (181393 / 200000) (181393 / 200000) x169 := by
    exact hx168
  let x170 : ℝ := Real.log x169
  have hx170 : Bounds (-97651419 / 1000000000) (-48825709 / 500000000) x170 := by
    exact bounds_log hx169 (by norm_num) (by simpa only [div_one] using reflection_log_4889.1) (by simpa only [div_one] using reflection_log_4889.2)
  let x171 : ℝ := x166*x170
  have hx171 : Bounds (-44283209617 / 500000000000) (-44283209163 / 500000000000) x171 := by
    apply bounds_mul hx166 hx170 <;> norm_num
  let x172 : ℝ := x163+x171
  have hx172 : Bounds (4334019847 / 500000000000) (270876303 / 31250000000) x172 := by
    apply bounds_add hx163 hx171 <;> norm_num
  let x173 : ℝ := (2 / 1)⁻¹
  have hx173 : Bounds (1 / 2) (1 / 2) x173 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x174 : ℝ := x172*x173
  have hx174 : Bounds (4334019847 / 1000000000000) (270876303 / 62500000000) x174 := by
    apply bounds_mul hx172 hx173 <;> norm_num
  let x175 : ℝ := x172/(2 / 1)
  have hx175 : Bounds (4334019847 / 1000000000000) (270876303 / 62500000000) x175 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx174
  let x176 : ℝ := -x175
  have hx176 : Bounds (-270876303 / 62500000000) (-4334019847 / 1000000000000) x176 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx175
  let x177 : ℝ := x159+x176
  have hx177 : Bounds (43050822447 / 62500000000) (688813161153 / 1000000000000) x177 := by
    apply bounds_add hx159 hx176 <;> norm_num
  let x178 : ℝ := x159-x175
  have hx178 : Bounds (43050822447 / 62500000000) (688813161153 / 1000000000000) x178 := by
    exact hx177
  let x179 : ℝ := biasE (18607 / 200000)
  have hx179 : Bounds (43050822447 / 62500000000) (688813161153 / 1000000000000) x179 := by
    simpa +zetaDelta only [biasE, div_one] using hx178
  let x180 : ℝ := biasE c
  have hx180 : Bounds (344395555553 / 500000000000) (688813161153 / 1000000000000) x180 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx158.1 hx179.2
  let x181 : ℝ := Real.log (2 / 1)
  have hx181 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x181 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x182 : ℝ := c*c
  have hx182 : Bounds (346220449 / 40000000000) (8699479441 / 1000000000000) x182 := by
    apply bounds_mul hc hc <;> norm_num
  let x183 : ℝ := -x182
  have hx183 : Bounds (-8699479441 / 1000000000000) (-346220449 / 40000000000) x183 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx182
  let x184 : ℝ := (1 / 1)+x183
  have hx184 : Bounds (991300520559 / 1000000000000) (39653779551 / 40000000000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx183 <;> norm_num
  let x185 : ℝ := (1 / 1)-x182
  have hx185 : Bounds (991300520559 / 1000000000000) (39653779551 / 40000000000) x185 := by
    exact hx184
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (-8737541 / 1000000000) (-8693187 / 1000000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_4892.1) (by simpa only [div_one] using reflection_log_4893.2)
  let x187 : ℝ := (2 / 1)⁻¹
  have hx187 : Bounds (1 / 2) (1 / 2) x187 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x188 : ℝ := x186*x187
  have hx188 : Bounds (-8737541 / 2000000000) (-8693187 / 2000000000) x188 := by
    apply bounds_mul hx186 hx187 <;> norm_num
  let x189 : ℝ := x186/(2 / 1)
  have hx189 : Bounds (-8737541 / 2000000000) (-8693187 / 2000000000) x189 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx188
  let x190 : ℝ := -x189
  have hx190 : Bounds (8693187 / 2000000000) (8737541 / 2000000000) x190 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx189
  let x191 : ℝ := x181+x190
  have hx191 : Bounds (1394987547 / 2000000000) (1395031903 / 2000000000) x191 := by
    apply bounds_add hx181 hx190 <;> norm_num
  let x192 : ℝ := x181-x189
  have hx192 : Bounds (1394987547 / 2000000000) (1395031903 / 2000000000) x192 := by
    exact hx191
  let x193 : ℝ := c*(1 / 1)
  have hx193 : Bounds (18607 / 200000) (93271 / 1000000) x193 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x194 : ℝ := c*x193
  have hx194 : Bounds (346220449 / 40000000000) (8699479441 / 1000000000000) x194 := by
    apply bounds_mul hc hx193 <;> norm_num
  let x195 : ℝ := c^2
  have hx195 : Bounds (346220449 / 40000000000) (8699479441 / 1000000000000) x195 := by
    (convert hx194 using 1; ring)
  let x196 : ℝ := -x195
  have hx196 : Bounds (-8699479441 / 1000000000000) (-346220449 / 40000000000) x196 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx195
  let x197 : ℝ := (1 / 1)+x196
  have hx197 : Bounds (991300520559 / 1000000000000) (39653779551 / 40000000000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx196 <;> norm_num
  let x198 : ℝ := (1 / 1)-x195
  have hx198 : Bounds (991300520559 / 1000000000000) (39653779551 / 40000000000) x198 := by
    exact hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (218607 / 200000) (1093271 / 1000000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-93271 / 1000000) (-18607 / 200000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (906729 / 1000000) (181393 / 200000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (906729 / 1000000) (181393 / 200000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (55128918977 / 50000000000) (551432677239 / 500000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (30128918977 / 25000000000) (301432677239 / 250000000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (30128918977 / 25000000000) (301432677239 / 250000000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (186609649 / 1000000000) (187085781 / 1000000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_4894.1) (by simpa only [div_one] using reflection_log_4895.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (186609649 / 2000000000) (187085781 / 2000000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (186609649 / 2000000000) (187085781 / 2000000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (1 / 1)+a
  have hx210 : Bounds (11851 / 10000) (2963 / 2500) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) ha <;> norm_num
  let x211 : ℝ := -a
  have hx211 : Bounds (-463 / 2500) (-1851 / 10000) x211 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg ha
  let x212 : ℝ := (1 / 1)+x211
  have hx212 : Bounds (2037 / 2500) (8149 / 10000) x212 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx211 <;> norm_num
  let x213 : ℝ := (1 / 1)-a
  have hx213 : Bounds (2037 / 2500) (8149 / 10000) x213 := by
    exact hx212
  let x214 : ℝ := x213⁻¹
  have hx214 : Bounds (1227144434899 / 1000000000000) (1227295041729 / 1000000000000) x214 := by
    apply bounds_inv hx213 <;> norm_num
  let x215 : ℝ := x210*x214
  have hx215 : Bounds (727144434899 / 500000000000) (727295041729 / 500000000000) x215 := by
    apply bounds_mul hx210 hx214 <;> norm_num
  let x216 : ℝ := x210/x213
  have hx216 : Bounds (727144434899 / 500000000000) (727295041729 / 500000000000) x216 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx215
  let x217 : ℝ := Real.log x216
  have hx217 : Bounds (374517031 / 1000000000) (93681033 / 250000000) x217 := by
    exact bounds_log hx216 (by norm_num) (by simpa only [div_one] using reflection_log_4896.1) (by simpa only [div_one] using reflection_log_4897.2)
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (374517031 / 2000000000) (93681033 / 500000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (374517031 / 2000000000) (93681033 / 500000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := (2 / 1)*x192
  have hx221 : Bounds (1394987547 / 1000000000) (1395031903 / 1000000000) x221 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x222 : ℝ := c*(1 / 1)
  have hx222 : Bounds (18607 / 200000) (93271 / 1000000) x222 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x223 : ℝ := c*x222
  have hx223 : Bounds (346220449 / 40000000000) (8699479441 / 1000000000000) x223 := by
    apply bounds_mul hc hx222 <;> norm_num
  let x224 : ℝ := c^2
  have hx224 : Bounds (346220449 / 40000000000) (8699479441 / 1000000000000) x224 := by
    (convert hx223 using 1; ring)
  let x225 : ℝ := -x224
  have hx225 : Bounds (-8699479441 / 1000000000000) (-346220449 / 40000000000) x225 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx224
  let x226 : ℝ := x221+x225
  have hx226 : Bounds (1386288067559 / 1000000000000) (55455055671 / 40000000000) x226 := by
    apply bounds_add hx221 hx225 <;> norm_num
  let x227 : ℝ := x221-x224
  have hx227 : Bounds (1386288067559 / 1000000000000) (55455055671 / 40000000000) x227 := by
    exact hx226
  let x228 : ℝ := x180*x227
  have hx228 : Bounds (477431449183 / 500000000000) (954954304967 / 1000000000000) x228 := by
    apply bounds_mul hx180 hx227 <;> norm_num
  let x229 : ℝ := (2 / 1)*x90
  have hx229 : Bounds (342261354167 / 250000000000) (136906416769 / 100000000000) x229 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x230 : ℝ := x198*(1 / 1)
  have hx230 : Bounds (991300520559 / 1000000000000) (39653779551 / 40000000000) x230 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x231 : ℝ := x198*x230
  have hx231 : Bounds (49133836103 / 50000000000) (39310555817 / 40000000000) x231 := by
    apply bounds_mul hx198 hx230 <;> norm_num
  let x232 : ℝ := x198^2
  have hx232 : Bounds (49133836103 / 50000000000) (39310555817 / 40000000000) x232 := by
    (convert hx231 using 1; ring)
  let x233 : ℝ := x229*x232
  have hx233 : Bounds (672664531201 / 500000000000) (672733417263 / 500000000000) x233 := by
    apply bounds_mul hx229 hx232 <;> norm_num
  let x234 : ℝ := x192*(1 / 1)
  have hx234 : Bounds (1394987547 / 2000000000) (1395031903 / 2000000000) x234 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x235 : ℝ := x192*x234
  have hx235 : Bounds (486497564071 / 1000000000000) (486528502597 / 1000000000000) x235 := by
    apply bounds_mul hx192 hx234 <;> norm_num
  let x236 : ℝ := x192*x235
  have hx236 : Bounds (169664510881 / 500000000000) (339361391421 / 1000000000000) x236 := by
    apply bounds_mul hx192 hx235 <;> norm_num
  let x237 : ℝ := x192^3
  have hx237 : Bounds (169664510881 / 500000000000) (339361391421 / 1000000000000) x237 := by
    (convert hx236 using 1; ring)
  let x238 : ℝ := x233*x237
  have hx238 : Bounds (114127298673 / 250000000000) (114149874269 / 250000000000) x238 := by
    apply bounds_mul hx233 hx237 <;> norm_num
  let x239 : ℝ := x238⁻¹
  have hx239 : Bounds (547525789233 / 250000000000) (2190536382679 / 1000000000000) x239 := by
    apply bounds_inv hx238 <;> norm_num
  let x240 : ℝ := x228*x239
  have hx240 : Bounds (522812062037 / 250000000000) (2091862148827 / 1000000000000) x240 := by
    apply bounds_mul hx228 hx239 <;> norm_num
  let x241 : ℝ := x228/x238
  have hx241 : Bounds (522812062037 / 250000000000) (2091862148827 / 1000000000000) x241 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx240
  let x242 : ℝ := -x209
  have hx242 : Bounds (-187085781 / 2000000000) (-186609649 / 2000000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x243 : ℝ := (2 / 1)*x192
  have hx243 : Bounds (1394987547 / 1000000000) (1395031903 / 1000000000) x243 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x244 : ℝ := c*(1 / 1)
  have hx244 : Bounds (18607 / 200000) (93271 / 1000000) x244 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x245 : ℝ := c*x244
  have hx245 : Bounds (346220449 / 40000000000) (8699479441 / 1000000000000) x245 := by
    apply bounds_mul hc hx244 <;> norm_num
  let x246 : ℝ := c^2
  have hx246 : Bounds (346220449 / 40000000000) (8699479441 / 1000000000000) x246 := by
    (convert hx245 using 1; ring)
  let x247 : ℝ := -x246
  have hx247 : Bounds (-8699479441 / 1000000000000) (-346220449 / 40000000000) x247 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx246
  let x248 : ℝ := x243+x247
  have hx248 : Bounds (1386288067559 / 1000000000000) (55455055671 / 40000000000) x248 := by
    apply bounds_add hx243 hx247 <;> norm_num
  let x249 : ℝ := x243-x246
  have hx249 : Bounds (1386288067559 / 1000000000000) (55455055671 / 40000000000) x249 := by
    exact hx248
  let x250 : ℝ := x242*x249
  have hx250 : Bounds (-4052676719 / 31250000000) (-2586947297 / 20000000000) x250 := by
    apply bounds_mul hx242 hx249 <;> norm_num
  let x251 : ℝ := x198⁻¹
  have hx251 : Bounds (1008731083213 / 1000000000000) (1008775824547 / 1000000000000) x251 := by
    apply bounds_inv hx198 <;> norm_num
  let x252 : ℝ := c*x251
  have hx252 : Bounds (46923648163 / 500000000000) (23522382483 / 250000000000) x252 := by
    apply bounds_mul hc hx251 <;> norm_num
  let x253 : ℝ := c/x198
  have hx253 : Bounds (46923648163 / 500000000000) (23522382483 / 250000000000) x253 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx252
  let x254 : ℝ := (2 / 1)*x253
  have hx254 : Bounds (46923648163 / 250000000000) (23522382483 / 125000000000) x254 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx253 <;> norm_num
  let x255 : ℝ := (2 / 1)*c
  have hx255 : Bounds (18607 / 100000) (93271 / 500000) x255 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hc <;> norm_num
  let x256 : ℝ := -x255
  have hx256 : Bounds (-93271 / 500000) (-18607 / 100000) x256 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx255
  let x257 : ℝ := x254+x256
  have hx257 : Bounds (288148163 / 250000000000) (263632483 / 125000000000) x257 := by
    apply bounds_add hx254 hx256 <;> norm_num
  let x258 : ℝ := x254-x255
  have hx258 : Bounds (288148163 / 250000000000) (263632483 / 125000000000) x258 := by
    exact hx257
  let x259 : ℝ := x180*x258
  have hx259 : Bounds (793895573 / 1000000000000) (45398381 / 31250000000) x259 := by
    apply bounds_mul hx180 hx258 <;> norm_num
  let x260 : ℝ := x250+x259
  have hx260 : Bounds (-25778351887 / 200000000000) (-63947308329 / 500000000000) x260 := by
    apply bounds_add hx250 hx259 <;> norm_num
  let x261 : ℝ := (2 / 1)*x90
  have hx261 : Bounds (342261354167 / 250000000000) (136906416769 / 100000000000) x261 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x262 : ℝ := x198*(1 / 1)
  have hx262 : Bounds (991300520559 / 1000000000000) (39653779551 / 40000000000) x262 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x263 : ℝ := x198*x262
  have hx263 : Bounds (49133836103 / 50000000000) (39310555817 / 40000000000) x263 := by
    apply bounds_mul hx198 hx262 <;> norm_num
  let x264 : ℝ := x198^2
  have hx264 : Bounds (49133836103 / 50000000000) (39310555817 / 40000000000) x264 := by
    (convert hx263 using 1; ring)
  let x265 : ℝ := x261*x264
  have hx265 : Bounds (672664531201 / 500000000000) (672733417263 / 500000000000) x265 := by
    apply bounds_mul hx261 hx264 <;> norm_num
  let x266 : ℝ := x192*(1 / 1)
  have hx266 : Bounds (1394987547 / 2000000000) (1395031903 / 2000000000) x266 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x267 : ℝ := x192*x266
  have hx267 : Bounds (486497564071 / 1000000000000) (486528502597 / 1000000000000) x267 := by
    apply bounds_mul hx192 hx266 <;> norm_num
  let x268 : ℝ := x192*x267
  have hx268 : Bounds (169664510881 / 500000000000) (339361391421 / 1000000000000) x268 := by
    apply bounds_mul hx192 hx267 <;> norm_num
  let x269 : ℝ := x192^3
  have hx269 : Bounds (169664510881 / 500000000000) (339361391421 / 1000000000000) x269 := by
    (convert hx268 using 1; ring)
  let x270 : ℝ := x265*x269
  have hx270 : Bounds (114127298673 / 250000000000) (114149874269 / 250000000000) x270 := by
    apply bounds_mul hx265 hx269 <;> norm_num
  let x271 : ℝ := x270⁻¹
  have hx271 : Bounds (547525789233 / 250000000000) (2190536382679 / 1000000000000) x271 := by
    apply bounds_inv hx270 <;> norm_num
  let x272 : ℝ := x260*x271
  have hx272 : Bounds (-28234208847 / 100000000000) (-280102403697 / 1000000000000) x272 := by
    apply bounds_mul hx260 hx271 <;> norm_num
  let x273 : ℝ := x260/x270
  have hx273 : Bounds (-28234208847 / 100000000000) (-280102403697 / 1000000000000) x273 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx272
  let x274 : ℝ := (4 / 1)*c
  have hx274 : Bounds (18607 / 50000) (93271 / 250000) x274 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hc <;> norm_num
  let x275 : ℝ := x198⁻¹
  have hx275 : Bounds (1008731083213 / 1000000000000) (1008775824547 / 1000000000000) x275 := by
    apply bounds_inv hx198 <;> norm_num
  let x276 : ℝ := x274*x275
  have hx276 : Bounds (187694592653 / 500000000000) (188179059863 / 500000000000) x276 := by
    apply bounds_mul hx274 hx275 <;> norm_num
  let x277 : ℝ := x274/x198
  have hx277 : Bounds (187694592653 / 500000000000) (188179059863 / 500000000000) x277 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx276
  let x278 : ℝ := (3 / 1)*c
  have hx278 : Bounds (55821 / 200000) (279813 / 1000000) x278 := by
    apply bounds_mul (bounds_const ((3 / 1) : ℝ)) hc <;> norm_num
  let x279 : ℝ := x198*x192
  have hx279 : Bounds (691425940757 / 1000000000000) (691478594353 / 1000000000000) x279 := by
    apply bounds_mul hx198 hx192 <;> norm_num
  let x280 : ℝ := x279⁻¹
  have hx280 : Bounds (1446176364917 / 1000000000000) (180785811801 / 125000000000) x280 := by
    apply bounds_inv hx279 <;> norm_num
  let x281 : ℝ := x278*x280
  have hx281 : Bounds (40363505433 / 100000000000) (20234488143 / 50000000000) x281 := by
    apply bounds_mul hx278 hx280 <;> norm_num
  let x282 : ℝ := x278/x279
  have hx282 : Bounds (40363505433 / 100000000000) (20234488143 / 50000000000) x282 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx281
  let x283 : ℝ := -x282
  have hx283 : Bounds (-20234488143 / 50000000000) (-40363505433 / 100000000000) x283 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx282
  let x284 : ℝ := x277+x283
  have hx284 : Bounds (-14650288777 / 500000000000) (-6819233651 / 250000000000) x284 := by
    apply bounds_add hx277 hx283 <;> norm_num
  let x285 : ℝ := x277-x282
  have hx285 : Bounds (-14650288777 / 500000000000) (-6819233651 / 250000000000) x285 := by
    exact hx284
  let x286 : ℝ := x241*x285
  have hx286 : Bounds (-15323192281 / 250000000000) (-11408568341 / 200000000000) x286 := by
    apply bounds_mul hx241 hx285 <;> norm_num
  let x287 : ℝ := x273+x286
  have hx287 : Bounds (-171817428797 / 500000000000) (-168572622701 / 500000000000) x287 := by
    apply bounds_add hx273 hx286 <;> norm_num
  let x288 : ℝ := (2 / 1)*x192
  have hx288 : Bounds (1394987547 / 1000000000) (1395031903 / 1000000000) x288 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x289 : ℝ := c*(1 / 1)
  have hx289 : Bounds (18607 / 200000) (93271 / 1000000) x289 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x290 : ℝ := c*x289
  have hx290 : Bounds (346220449 / 40000000000) (8699479441 / 1000000000000) x290 := by
    apply bounds_mul hc hx289 <;> norm_num
  let x291 : ℝ := c^2
  have hx291 : Bounds (346220449 / 40000000000) (8699479441 / 1000000000000) x291 := by
    (convert hx290 using 1; ring)
  let x292 : ℝ := -x291
  have hx292 : Bounds (-8699479441 / 1000000000000) (-346220449 / 40000000000) x292 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx291
  let x293 : ℝ := x288+x292
  have hx293 : Bounds (1386288067559 / 1000000000000) (55455055671 / 40000000000) x293 := by
    apply bounds_add hx288 hx292 <;> norm_num
  let x294 : ℝ := x288-x291
  have hx294 : Bounds (1386288067559 / 1000000000000) (55455055671 / 40000000000) x294 := by
    exact hx293
  let x295 : ℝ := c*x294
  have hx295 : Bounds (25794662073 / 200000000000) (64654356219 / 500000000000) x295 := by
    apply bounds_mul hc hx294 <;> norm_num
  let x296 : ℝ := x198*(1 / 1)
  have hx296 : Bounds (991300520559 / 1000000000000) (39653779551 / 40000000000) x296 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x297 : ℝ := x198*x296
  have hx297 : Bounds (49133836103 / 50000000000) (39310555817 / 40000000000) x297 := by
    apply bounds_mul hx198 hx296 <;> norm_num
  let x298 : ℝ := x198^2
  have hx298 : Bounds (49133836103 / 50000000000) (39310555817 / 40000000000) x298 := by
    (convert hx297 using 1; ring)
  let x299 : ℝ := x192*(1 / 1)
  have hx299 : Bounds (1394987547 / 2000000000) (1395031903 / 2000000000) x299 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x300 : ℝ := x192*x299
  have hx300 : Bounds (486497564071 / 1000000000000) (486528502597 / 1000000000000) x300 := by
    apply bounds_mul hx192 hx299 <;> norm_num
  let x301 : ℝ := x192^2
  have hx301 : Bounds (486497564071 / 1000000000000) (486528502597 / 1000000000000) x301 := by
    (convert hx300 using 1; ring)
  let x302 : ℝ := x298*x301
  have hx302 : Bounds (478069831551 / 1000000000000) (29883915403 / 62500000000) x302 := by
    apply bounds_mul hx298 hx301 <;> norm_num
  let x303 : ℝ := x302⁻¹
  have hx303 : Bounds (2091426078449 / 1000000000000) (209174462391 / 100000000000) x303 := by
    apply bounds_inv hx302 <;> norm_num
  let x304 : ℝ := x295*x303
  have hx304 : Bounds (269738144721 / 1000000000000) (270480804067 / 1000000000000) x304 := by
    apply bounds_mul hx295 hx303 <;> norm_num
  let x305 : ℝ := x295/x302
  have hx305 : Bounds (269738144721 / 1000000000000) (270480804067 / 1000000000000) x305 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx304
  let x306 : ℝ := c*x220
  have hx306 : Bounds (17421595989 / 1000000000000) (8737723629 / 500000000000) x306 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x307 : ℝ := x180+x306
  have hx307 : Bounds (141242541419 / 200000000000) (706288608411 / 1000000000000) x307 := by
    apply bounds_add hx180 hx306 <;> norm_num
  let x308 : ℝ := x307*(1 / 1)
  have hx308 : Bounds (141242541419 / 200000000000) (706288608411 / 1000000000000) x308 := by
    apply bounds_mul hx307 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x309 : ℝ := x307*x308
  have hx309 : Bounds (249368193831 / 500000000000) (124710899593 / 250000000000) x309 := by
    apply bounds_mul hx307 hx308 <;> norm_num
  let x310 : ℝ := x307^2
  have hx310 : Bounds (249368193831 / 500000000000) (124710899593 / 250000000000) x310 := by
    (convert hx309 using 1; ring)
  let x311 : ℝ := x287*x310
  have hx311 : Bounds (-171420048889 / 1000000000000) (-168146601809 / 1000000000000) x311 := by
    apply bounds_mul hx287 hx310 <;> norm_num
  let x312 : ℝ := (2 / 1)*x241
  have hx312 : Bounds (522812062037 / 125000000000) (2091862148827 / 500000000000) x312 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx241 <;> norm_num
  let x313 : ℝ := c*x220
  have hx313 : Bounds (17421595989 / 1000000000000) (8737723629 / 500000000000) x313 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x314 : ℝ := x180+x313
  have hx314 : Bounds (141242541419 / 200000000000) (706288608411 / 1000000000000) x314 := by
    apply bounds_add hx180 hx313 <;> norm_num
  let x315 : ℝ := x312*x314
  have hx315 : Bounds (369216521633 / 125000000000) (1477458406083 / 500000000000) x315 := by
    apply bounds_mul hx312 hx314 <;> norm_num
  let x316 : ℝ := -x209
  have hx316 : Bounds (-187085781 / 2000000000) (-186609649 / 2000000000) x316 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x317 : ℝ := x220+x316
  have hx317 : Bounds (29989 / 320000) (188114483 / 2000000000) x317 := by
    apply bounds_add hx220 hx316 <;> norm_num
  let x318 : ℝ := x220-x209
  have hx318 : Bounds (29989 / 320000) (188114483 / 2000000000) x318 := by
    exact hx317
  let x319 : ℝ := x315*x318
  have hx319 : Bounds (276810856681 / 1000000000000) (55586264843 / 200000000000) x319 := by
    apply bounds_mul hx315 hx318 <;> norm_num
  let x320 : ℝ := x311+x319
  have hx320 : Bounds (6586925487 / 62500000000) (54892361203 / 500000000000) x320 := by
    apply bounds_add hx311 hx319 <;> norm_num
  let x321 : ℝ := a*(1 / 1)
  have hx321 : Bounds (1851 / 10000) (463 / 2500) x321 := by
    apply bounds_mul ha (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x322 : ℝ := a*x321
  have hx322 : Bounds (3426201 / 100000000) (214369 / 6250000) x322 := by
    apply bounds_mul ha hx321 <;> norm_num
  let x323 : ℝ := a^2
  have hx323 : Bounds (3426201 / 100000000) (214369 / 6250000) x323 := by
    (convert hx322 using 1; ring)
  let x324 : ℝ := -x323
  have hx324 : Bounds (-214369 / 6250000) (-3426201 / 100000000) x324 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx323
  let x325 : ℝ := (1 / 1)+x324
  have hx325 : Bounds (6035631 / 6250000) (96573799 / 100000000) x325 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx324 <;> norm_num
  let x326 : ℝ := (1 / 1)-x323
  have hx326 : Bounds (6035631 / 6250000) (96573799 / 100000000) x326 := by
    exact hx325
  let x327 : ℝ := x326⁻¹
  have hx327 : Bounds (207095508379 / 200000000000) (1035517247493 / 1000000000000) x327 := by
    apply bounds_inv hx326 <;> norm_num
  let x328 : ℝ := (1 / 1)*x327
  have hx328 : Bounds (207095508379 / 200000000000) (1035517247493 / 1000000000000) x328 := by
    apply bounds_mul (bounds_const ((1 / 1) : ℝ)) hx327 <;> norm_num
  let x329 : ℝ := (1 / 1)/x326
  have hx329 : Bounds (207095508379 / 200000000000) (1035517247493 / 1000000000000) x329 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx328
  let x330 : ℝ := x329*x305
  have hx330 : Bounds (279307791051 / 1000000000000) (4376367777 / 15625000000) x330 := by
    apply bounds_mul hx329 hx305 <;> norm_num
  let x331 : ℝ := x320+x330
  have hx331 : Bounds (384698598843 / 1000000000000) (194936130067 / 500000000000) x331 := by
    apply bounds_add hx320 hx330 <;> norm_num
  let x332 : ℝ := x180*(1 / 1)
  have hx332 : Bounds (344395555553 / 500000000000) (688813161153 / 1000000000000) x332 := by
    apply bounds_mul hx180 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x333 : ℝ := x180*x332
  have hx333 : Bounds (237216597369 / 500000000000) (237231785489 / 500000000000) x333 := by
    apply bounds_mul hx180 hx332 <;> norm_num
  let x334 : ℝ := x180^2
  have hx334 : Bounds (237216597369 / 500000000000) (237231785489 / 500000000000) x334 := by
    (convert hx333 using 1; ring)
  let x335 : ℝ := x331*x334
  have hx335 : Bounds (9125689263 / 50000000000) (184980184769 / 1000000000000) x335 := by
    apply bounds_mul hx331 hx334 <;> norm_num
  let x336 : ℝ := x90*x192
  have hx336 : Bounds (238725163441 / 500000000000) (119368011949 / 250000000000) x336 := by
    apply bounds_mul hx90 hx192 <;> norm_num
  let x337 : ℝ := x336⁻¹
  have hx337 : Bounds (1047181719449 / 500000000000) (2094458718943 / 1000000000000) x337 := by
    apply bounds_inv hx336 <;> norm_num
  let x338 : ℝ := x335*x337
  have hx338 : Bounds (382250198943 / 1000000000000) (193716680411 / 500000000000) x338 := by
    apply bounds_mul hx335 hx337 <;> norm_num
  let x339 : ℝ := x335/x336
  have hx339 : Bounds (382250198943 / 1000000000000) (193716680411 / 500000000000) x339 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx338
  have hu : x339 < (3657698358973465937451856811 / 9326498653292401000000000000) := lt_of_le_of_lt hx339.2 (by norm_num)
  simpa +zetaDelta only [ScFormula,Kprime,K,Mprime,SmallMean.A,biasB,div_one,pow_two] using hu

open GeneralCK.Reflection
/-- Uniform derivative enclosure including input boxes with z=0. -/
theorem derivative_bound_351 {a z s : ℝ}
    (ha : a ∈ Set.Icc ((1851 / 10000):ℝ) ((463 / 2500)))
    (hz : z ∈ Set.Icc (0:ℝ) (1/1000))
    (hs : s ∈ Set.Ioo (a*(1-z)/2) (a*(1+z)/2)) :
    P a ((biasE a+biasE (a*z))/2) s ≤ (3657698358973465937451856811 / 9326498653292401000000000000) := by
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
  have hsl : (1849149 / 20000000) ≤ s := by
    have h := mul_le_mul ha.1 (show (999/1000:ℝ) ≤ 1-z by linarith [hz.2])
      (by norm_num : (0:ℝ) ≤ 999/1000) ha0.le
    nlinarith [hs.1]
  have hsu : s ≤ (463463 / 5000000) := by
    have h := mul_le_mul ha.2 (show 1+z ≤ (1001/1000:ℝ) by linarith [hz.2])
      (by linarith [hz.1] : 0 ≤ 1+z) (by norm_num : (0:ℝ) ≤ (463 / 2500))
    nlinarith [hs.2]
  have hy := div_pos he hs0
  have hc := biasContact_mem hy
  have heq : biasE (biasContact (((biasE a+biasE (a*z))/2)/s)) =
      (((biasE a+biasE (a*z))/2)/s)*biasContact (((biasE a+biasE (a*z))/2)/s) := by
    exact (div_eq_iff hc.1.ne').mp (biasR_biasContact hy)
  have hb := derivative_leaf_351 a z s _ ha hz ⟨hsl,hsu⟩ hc.1.le hc.2.le heq
  rw [P_eq_formula ha0 ha1 he hs0]
  exact hb.le

/-- Checked low-ratio strip: includes arbitrarily small positive z. -/
theorem curvature_leaf_351 {a z : ℝ}
    (ha : a ∈ Set.Icc ((1851 / 10000):ℝ) ((463 / 2500)))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < curvature a (a*z) := by
  have ha0 : 0 < a := by linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  apply curvature_pos_of_derivative_bound ha0 ha1 hz.1 (by linarith [hz.2])
    (fun s hs => derivative_bound_351 ha ⟨hz.1.le,hz.2⟩ hs) (M := (3657698358973465937451856811 / 9326498653292401000000000000))
  exact lt_of_lt_of_le (by norm_num : (3657698358973465937451856811 / 9326498653292401000000000000) < 2*((1851 / 10000):ℝ)/(1-((1851 / 10000):ℝ)^2)^2)
    (base_mono (by norm_num) ha.1 ha1)

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Cell0352 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
theorem derivative_leaf_352 (a z s c : ℝ)
    (ha : Bounds (463 / 2500) (1853 / 10000) a) (hz : Bounds 0 (1/1000) z)
    (hs : Bounds (462537 / 5000000) (1854853 / 20000000) s) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (heq : biasE c = (((biasE a+biasE (a*z))/2)/s)*c) :
    ScFormula c a ((biasE a+biasE (a*z))/2)*(biasE c)^2 /
      (((biasE a+biasE (a*z))/2)*biasB c) < (28590672898290095241828587 / 72857683136322000000000000) := by
  let x0 : ℝ := Real.log (2 / 1)
  have hx0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x0 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x1 : ℝ := (1 / 1)+(1853 / 10000)
  have hx1 : Bounds (11853 / 10000) (11853 / 10000) x1 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1853 / 10000) : ℝ)) <;> norm_num
  let x2 : ℝ := (1 / 1)+(1853 / 10000)
  have hx2 : Bounds (11853 / 10000) (11853 / 10000) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1853 / 10000) : ℝ)) <;> norm_num
  let x3 : ℝ := Real.log x2
  have hx3 : Bounds (169995907 / 1000000000) (42498977 / 250000000) x3 := by
    exact bounds_log hx2 (by norm_num) (by simpa only [div_one] using reflection_log_4898.1) (by simpa only [div_one] using reflection_log_4898.2)
  let x4 : ℝ := x1*x3
  have hx4 : Bounds (201496148567 / 1000000000000) (201496149753 / 1000000000000) x4 := by
    apply bounds_mul hx1 hx3 <;> norm_num
  let x5 : ℝ := -(1853 / 10000)
  have hx5 : Bounds (-1853 / 10000) (-1853 / 10000) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1853 / 10000) : ℝ))
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (8147 / 10000) (8147 / 10000) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-(1853 / 10000)
  have hx7 : Bounds (8147 / 10000) (8147 / 10000) x7 := by
    exact hx6
  let x8 : ℝ := -(1853 / 10000)
  have hx8 : Bounds (-1853 / 10000) (-1853 / 10000) x8 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1853 / 10000) : ℝ))
  let x9 : ℝ := (1 / 1)+x8
  have hx9 : Bounds (8147 / 10000) (8147 / 10000) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx8 <;> norm_num
  let x10 : ℝ := (1 / 1)-(1853 / 10000)
  have hx10 : Bounds (8147 / 10000) (8147 / 10000) x10 := by
    exact hx9
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (-51233833 / 250000000) (-204935331 / 1000000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_4899.1) (by simpa only [div_one] using reflection_log_4899.2)
  let x12 : ℝ := x7*x11
  have hx12 : Bounds (-166960814981 / 1000000000000) (-33392162833 / 200000000000) x12 := by
    apply bounds_mul hx7 hx11 <;> norm_num
  let x13 : ℝ := x4+x12
  have hx13 : Bounds (17267666793 / 500000000000) (8633833897 / 250000000000) x13 := by
    apply bounds_add hx4 hx12 <;> norm_num
  let x14 : ℝ := (2 / 1)⁻¹
  have hx14 : Bounds (1 / 2) (1 / 2) x14 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x15 : ℝ := x13*x14
  have hx15 : Bounds (17267666793 / 1000000000000) (8633833897 / 500000000000) x15 := by
    apply bounds_mul hx13 hx14 <;> norm_num
  let x16 : ℝ := x13/(2 / 1)
  have hx16 : Bounds (17267666793 / 1000000000000) (8633833897 / 500000000000) x16 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx15
  let x17 : ℝ := -x16
  have hx17 : Bounds (-8633833897 / 500000000000) (-17267666793 / 1000000000000) x17 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx16
  let x18 : ℝ := x0+x17
  have hx18 : Bounds (337939756103 / 500000000000) (675879514207 / 1000000000000) x18 := by
    apply bounds_add hx0 hx17 <;> norm_num
  let x19 : ℝ := x0-x16
  have hx19 : Bounds (337939756103 / 500000000000) (675879514207 / 1000000000000) x19 := by
    exact hx18
  let x20 : ℝ := biasE (1853 / 10000)
  have hx20 : Bounds (337939756103 / 500000000000) (675879514207 / 1000000000000) x20 := by
    simpa +zetaDelta only [biasE, div_one] using hx19
  let x21 : ℝ := Real.log (2 / 1)
  have hx21 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x21 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x22 : ℝ := (1 / 1)+(463 / 2500)
  have hx22 : Bounds (2963 / 2500) (2963 / 2500) x22 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((463 / 2500) : ℝ)) <;> norm_num
  let x23 : ℝ := (1 / 1)+(463 / 2500)
  have hx23 : Bounds (2963 / 2500) (2963 / 2500) x23 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((463 / 2500) : ℝ)) <;> norm_num
  let x24 : ℝ := Real.log x23
  have hx24 : Bounds (10619471 / 62500000) (169911537 / 1000000000) x24 := by
    exact bounds_log hx23 (by norm_num) (by simpa only [div_one] using reflection_log_4884.1) (by simpa only [div_one] using reflection_log_4884.2)
  let x25 : ℝ := x22*x24
  have hx25 : Bounds (201379152467 / 1000000000000) (201379153653 / 1000000000000) x25 := by
    apply bounds_mul hx22 hx24 <;> norm_num
  let x26 : ℝ := -(463 / 2500)
  have hx26 : Bounds (-463 / 2500) (-463 / 2500) x26 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((463 / 2500) : ℝ))
  let x27 : ℝ := (1 / 1)+x26
  have hx27 : Bounds (2037 / 2500) (2037 / 2500) x27 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx26 <;> norm_num
  let x28 : ℝ := (1 / 1)-(463 / 2500)
  have hx28 : Bounds (2037 / 2500) (2037 / 2500) x28 := by
    exact hx27
  let x29 : ℝ := -(463 / 2500)
  have hx29 : Bounds (-463 / 2500) (-463 / 2500) x29 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((463 / 2500) : ℝ))
  let x30 : ℝ := (1 / 1)+x29
  have hx30 : Bounds (2037 / 2500) (2037 / 2500) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx29 <;> norm_num
  let x31 : ℝ := (1 / 1)-(463 / 2500)
  have hx31 : Bounds (2037 / 2500) (2037 / 2500) x31 := by
    exact hx30
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (-40962519 / 200000000) (-102406297 / 500000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_4885.1) (by simpa only [div_one] using reflection_log_4885.2)
  let x33 : ℝ := x28*x32
  have hx33 : Bounds (-83440651203 / 500000000000) (-166881301591 / 1000000000000) x33 := by
    apply bounds_mul hx28 hx32 <;> norm_num
  let x34 : ℝ := x25+x33
  have hx34 : Bounds (34497850061 / 1000000000000) (17248926031 / 500000000000) x34 := by
    apply bounds_add hx25 hx33 <;> norm_num
  let x35 : ℝ := (2 / 1)⁻¹
  have hx35 : Bounds (1 / 2) (1 / 2) x35 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x36 : ℝ := x34*x35
  have hx36 : Bounds (1724892503 / 100000000000) (17248926031 / 1000000000000) x36 := by
    apply bounds_mul hx34 hx35 <;> norm_num
  let x37 : ℝ := x34/(2 / 1)
  have hx37 : Bounds (1724892503 / 100000000000) (17248926031 / 1000000000000) x37 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx36
  let x38 : ℝ := -x37
  have hx38 : Bounds (-17248926031 / 1000000000000) (-1724892503 / 100000000000) x38 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx37
  let x39 : ℝ := x21+x38
  have hx39 : Bounds (675898253969 / 1000000000000) (67589825597 / 100000000000) x39 := by
    apply bounds_add hx21 hx38 <;> norm_num
  let x40 : ℝ := x21-x37
  have hx40 : Bounds (675898253969 / 1000000000000) (67589825597 / 100000000000) x40 := by
    exact hx39
  let x41 : ℝ := biasE (463 / 2500)
  have hx41 : Bounds (675898253969 / 1000000000000) (67589825597 / 100000000000) x41 := by
    simpa +zetaDelta only [biasE, div_one] using hx40
  let x42 : ℝ := biasE a
  have hx42 : Bounds (337939756103 / 500000000000) (67589825597 / 100000000000) x42 := by
    exact bounds_biasE ha (by norm_num) (by norm_num) hx20.1 hx41.2
  let x43 : ℝ := a*z
  have hx43 : Bounds (0 / 1) (1853 / 10000000) x43 := by
    apply bounds_mul ha hz <;> norm_num
  let x44 : ℝ := Real.log (2 / 1)
  have hx44 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x44 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x45 : ℝ := (1 / 1)+(1853 / 10000000)
  have hx45 : Bounds (10001853 / 10000000) (10001853 / 10000000) x45 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1853 / 10000000) : ℝ)) <;> norm_num
  let x46 : ℝ := (1 / 1)+(1853 / 10000000)
  have hx46 : Bounds (10001853 / 10000000) (10001853 / 10000000) x46 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1853 / 10000000) : ℝ)) <;> norm_num
  let x47 : ℝ := Real.log x46
  have hx47 : Bounds (92641 / 500000000) (185283 / 1000000000) x47 := by
    exact bounds_log hx46 (by norm_num) (by simpa only [div_one] using reflection_log_4900.1) (by simpa only [div_one] using reflection_log_4900.2)
  let x48 : ℝ := x45*x47
  have hx48 : Bounds (46329083 / 250000000000) (185317333 / 1000000000000) x48 := by
    apply bounds_mul hx45 hx47 <;> norm_num
  let x49 : ℝ := -(1853 / 10000000)
  have hx49 : Bounds (-1853 / 10000000) (-1853 / 10000000) x49 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1853 / 10000000) : ℝ))
  let x50 : ℝ := (1 / 1)+x49
  have hx50 : Bounds (9998147 / 10000000) (9998147 / 10000000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx49 <;> norm_num
  let x51 : ℝ := (1 / 1)-(1853 / 10000000)
  have hx51 : Bounds (9998147 / 10000000) (9998147 / 10000000) x51 := by
    exact hx50
  let x52 : ℝ := -(1853 / 10000000)
  have hx52 : Bounds (-1853 / 10000000) (-1853 / 10000000) x52 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1853 / 10000000) : ℝ))
  let x53 : ℝ := (1 / 1)+x52
  have hx53 : Bounds (9998147 / 10000000) (9998147 / 10000000) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx52 <;> norm_num
  let x54 : ℝ := (1 / 1)-(1853 / 10000000)
  have hx54 : Bounds (9998147 / 10000000) (9998147 / 10000000) x54 := by
    exact hx53
  let x55 : ℝ := Real.log x54
  have hx55 : Bounds (-92659 / 500000000) (-185317 / 1000000000) x55 := by
    exact bounds_log hx54 (by norm_num) (by simpa only [div_one] using reflection_log_4901.1) (by simpa only [div_one] using reflection_log_4901.2)
  let x56 : ℝ := x51*x55
  have hx56 : Bounds (-185283661 / 1000000000000) (-9264133 / 50000000000) x56 := by
    apply bounds_mul hx51 hx55 <;> norm_num
  let x57 : ℝ := x48+x56
  have hx57 : Bounds (32671 / 1000000000000) (34673 / 1000000000000) x57 := by
    apply bounds_add hx48 hx56 <;> norm_num
  let x58 : ℝ := (2 / 1)⁻¹
  have hx58 : Bounds (1 / 2) (1 / 2) x58 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x59 : ℝ := x57*x58
  have hx59 : Bounds (3267 / 200000000000) (17337 / 1000000000000) x59 := by
    apply bounds_mul hx57 hx58 <;> norm_num
  let x60 : ℝ := x57/(2 / 1)
  have hx60 : Bounds (3267 / 200000000000) (17337 / 1000000000000) x60 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx59
  let x61 : ℝ := -x60
  have hx61 : Bounds (-17337 / 1000000000000) (-3267 / 200000000000) x61 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx60
  let x62 : ℝ := x44+x61
  have hx62 : Bounds (693147162663 / 1000000000000) (138629432933 / 200000000000) x62 := by
    apply bounds_add hx44 hx61 <;> norm_num
  let x63 : ℝ := x44-x60
  have hx63 : Bounds (693147162663 / 1000000000000) (138629432933 / 200000000000) x63 := by
    exact hx62
  let x64 : ℝ := biasE (1853 / 10000000)
  have hx64 : Bounds (693147162663 / 1000000000000) (138629432933 / 200000000000) x64 := by
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
  have hx86 : Bounds (693147162663 / 1000000000000) (693147181 / 1000000000) x86 := by
    exact bounds_biasE hx43 (by norm_num) (by norm_num) hx64.1 hx85.2
  let x87 : ℝ := x42+x86
  have hx87 : Bounds (1369026674869 / 1000000000000) (136904543697 / 100000000000) x87 := by
    apply bounds_add hx42 hx86 <;> norm_num
  let x88 : ℝ := (2 / 1)⁻¹
  have hx88 : Bounds (1 / 2) (1 / 2) x88 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x89 : ℝ := x87*x88
  have hx89 : Bounds (342256668717 / 500000000000) (136904543697 / 200000000000) x89 := by
    apply bounds_mul hx87 hx88 <;> norm_num
  let x90 : ℝ := x87/(2 / 1)
  have hx90 : Bounds (342256668717 / 500000000000) (136904543697 / 200000000000) x90 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx89
  let x91 : ℝ := s⁻¹
  have hx91 : Bounds (2695631405831 / 250000000000) (1080994601513 / 100000000000) x91 := by
    apply bounds_inv hs <;> norm_num
  let x92 : ℝ := x90*x91
  have hx92 : Bounds (7380782600389 / 1000000000000) (7399653632953 / 1000000000000) x92 := by
    apply bounds_mul hx90 hx91 <;> norm_num
  let x93 : ℝ := x90/s
  have hx93 : Bounds (7380782600389 / 1000000000000) (7399653632953 / 1000000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(46543 / 500000)
  have hx95 : Bounds (546543 / 500000) (546543 / 500000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((46543 / 500000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(46543 / 500000)
  have hx96 : Bounds (546543 / 500000) (546543 / 500000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((46543 / 500000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (11125611 / 125000000) (89004889 / 1000000000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_4902.1) (by simpa only [div_one] using reflection_log_4902.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (24322499251 / 250000000000) (48644999049 / 500000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(46543 / 500000)
  have hx99 : Bounds (-46543 / 500000) (-46543 / 500000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((46543 / 500000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (453457 / 500000) (453457 / 500000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(46543 / 500000)
  have hx101 : Bounds (453457 / 500000) (453457 / 500000) x101 := by
    exact hx100
  let x102 : ℝ := -(46543 / 500000)
  have hx102 : Bounds (-46543 / 500000) (-46543 / 500000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((46543 / 500000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (453457 / 500000) (453457 / 500000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(46543 / 500000)
  have hx104 : Bounds (453457 / 500000) (453457 / 500000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-24426913 / 250000000) (-97707651 / 1000000000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_4903.1) (by simpa only [div_one] using reflection_log_4903.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-44306218753 / 500000000000) (-88612436599 / 1000000000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (4338779749 / 500000000000) (8677561499 / 1000000000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (4338779749 / 1000000000000) (17355123 / 4000000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (4338779749 / 1000000000000) (17355123 / 4000000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-17355123 / 4000000000) (-4338779749 / 1000000000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (2755233597 / 4000000000) (688808401251 / 1000000000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (2755233597 / 4000000000) (688808401251 / 1000000000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (46543 / 500000)
  have hx114 : Bounds (2755233597 / 4000000000) (688808401251 / 1000000000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(46661 / 500000)
  have hx116 : Bounds (546661 / 500000) (546661 / 500000) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((46661 / 500000) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(46661 / 500000)
  have hx117 : Bounds (546661 / 500000) (546661 / 500000) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((46661 / 500000) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (89220767 / 1000000000) (2788149 / 31250000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_4904.1) (by simpa only [div_one] using reflection_log_4904.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (97547027417 / 1000000000000) (3048344641 / 31250000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(46661 / 500000)
  have hx120 : Bounds (-46661 / 500000) (-46661 / 500000) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((46661 / 500000) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (453339 / 500000) (453339 / 500000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(46661 / 500000)
  have hx122 : Bounds (453339 / 500000) (453339 / 500000) x122 := by
    exact hx121
  let x123 : ℝ := -(46661 / 500000)
  have hx123 : Bounds (-46661 / 500000) (-46661 / 500000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((46661 / 500000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (453339 / 500000) (453339 / 500000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(46661 / 500000)
  have hx125 : Bounds (453339 / 500000) (453339 / 500000) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-97967909 / 1000000000) (-24491977 / 250000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_4905.1) (by simpa only [div_one] using reflection_log_4905.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-88825347797 / 1000000000000) (-88825346889 / 1000000000000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (436083981 / 50000000000) (8721681623 / 1000000000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (436083981 / 100000000000) (1090210203 / 250000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (436083981 / 100000000000) (1090210203 / 250000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-1090210203 / 250000000000) (-436083981 / 100000000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (172196584797 / 250000000000) (68878634119 / 100000000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (172196584797 / 250000000000) (68878634119 / 100000000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (46661 / 500000)
  have hx135 : Bounds (172196584797 / 250000000000) (68878634119 / 100000000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(46543 / 500000)
  have hx136 : Bounds (687047529139 / 1000000000000) (344402079039 / 500000000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((46543 / 500000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(46661 / 500000)
  have hx137 : Bounds (688789393833 / 1000000000000) (138110095267 / 200000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((46661 / 500000) : ℝ)) <;> norm_num
  have hc : Bounds (46543 / 500000) (46661 / 500000) c := by
    apply contact_bracket hc0 hc1 (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x93 by linarith [hx93.1])
      (show biasE c = x93*c by simpa +zetaDelta only [div_one] using heq)
    · have h1 : x93*(46543 / 500000) ≤ (344402079039 / 500000000000) := hx136.2
      have h2 : (2755233597 / 4000000000) ≤ biasE (46543 / 500000) := hx114.1
      linarith
    · have h1 : biasE (46661 / 500000) ≤ (68878634119 / 100000000000) := hx135.2
      have h2 : (688789393833 / 1000000000000) ≤ x93*(46661 / 500000) := hx137.1
      linarith
  let x138 : ℝ := Real.log (2 / 1)
  have hx138 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x138 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x139 : ℝ := (1 / 1)+(46661 / 500000)
  have hx139 : Bounds (546661 / 500000) (546661 / 500000) x139 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((46661 / 500000) : ℝ)) <;> norm_num
  let x140 : ℝ := (1 / 1)+(46661 / 500000)
  have hx140 : Bounds (546661 / 500000) (546661 / 500000) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((46661 / 500000) : ℝ)) <;> norm_num
  let x141 : ℝ := Real.log x140
  have hx141 : Bounds (89220767 / 1000000000) (2788149 / 31250000) x141 := by
    exact bounds_log hx140 (by norm_num) (by simpa only [div_one] using reflection_log_4904.1) (by simpa only [div_one] using reflection_log_4904.2)
  let x142 : ℝ := x139*x141
  have hx142 : Bounds (97547027417 / 1000000000000) (3048344641 / 31250000000) x142 := by
    apply bounds_mul hx139 hx141 <;> norm_num
  let x143 : ℝ := -(46661 / 500000)
  have hx143 : Bounds (-46661 / 500000) (-46661 / 500000) x143 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((46661 / 500000) : ℝ))
  let x144 : ℝ := (1 / 1)+x143
  have hx144 : Bounds (453339 / 500000) (453339 / 500000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx143 <;> norm_num
  let x145 : ℝ := (1 / 1)-(46661 / 500000)
  have hx145 : Bounds (453339 / 500000) (453339 / 500000) x145 := by
    exact hx144
  let x146 : ℝ := -(46661 / 500000)
  have hx146 : Bounds (-46661 / 500000) (-46661 / 500000) x146 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((46661 / 500000) : ℝ))
  let x147 : ℝ := (1 / 1)+x146
  have hx147 : Bounds (453339 / 500000) (453339 / 500000) x147 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx146 <;> norm_num
  let x148 : ℝ := (1 / 1)-(46661 / 500000)
  have hx148 : Bounds (453339 / 500000) (453339 / 500000) x148 := by
    exact hx147
  let x149 : ℝ := Real.log x148
  have hx149 : Bounds (-97967909 / 1000000000) (-24491977 / 250000000) x149 := by
    exact bounds_log hx148 (by norm_num) (by simpa only [div_one] using reflection_log_4905.1) (by simpa only [div_one] using reflection_log_4905.2)
  let x150 : ℝ := x145*x149
  have hx150 : Bounds (-88825347797 / 1000000000000) (-88825346889 / 1000000000000) x150 := by
    apply bounds_mul hx145 hx149 <;> norm_num
  let x151 : ℝ := x142+x150
  have hx151 : Bounds (436083981 / 50000000000) (8721681623 / 1000000000000) x151 := by
    apply bounds_add hx142 hx150 <;> norm_num
  let x152 : ℝ := (2 / 1)⁻¹
  have hx152 : Bounds (1 / 2) (1 / 2) x152 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x153 : ℝ := x151*x152
  have hx153 : Bounds (436083981 / 100000000000) (1090210203 / 250000000000) x153 := by
    apply bounds_mul hx151 hx152 <;> norm_num
  let x154 : ℝ := x151/(2 / 1)
  have hx154 : Bounds (436083981 / 100000000000) (1090210203 / 250000000000) x154 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx153
  let x155 : ℝ := -x154
  have hx155 : Bounds (-1090210203 / 250000000000) (-436083981 / 100000000000) x155 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx154
  let x156 : ℝ := x138+x155
  have hx156 : Bounds (172196584797 / 250000000000) (68878634119 / 100000000000) x156 := by
    apply bounds_add hx138 hx155 <;> norm_num
  let x157 : ℝ := x138-x154
  have hx157 : Bounds (172196584797 / 250000000000) (68878634119 / 100000000000) x157 := by
    exact hx156
  let x158 : ℝ := biasE (46661 / 500000)
  have hx158 : Bounds (172196584797 / 250000000000) (68878634119 / 100000000000) x158 := by
    simpa +zetaDelta only [biasE, div_one] using hx157
  let x159 : ℝ := Real.log (2 / 1)
  have hx159 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x159 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x160 : ℝ := (1 / 1)+(46543 / 500000)
  have hx160 : Bounds (546543 / 500000) (546543 / 500000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((46543 / 500000) : ℝ)) <;> norm_num
  let x161 : ℝ := (1 / 1)+(46543 / 500000)
  have hx161 : Bounds (546543 / 500000) (546543 / 500000) x161 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((46543 / 500000) : ℝ)) <;> norm_num
  let x162 : ℝ := Real.log x161
  have hx162 : Bounds (11125611 / 125000000) (89004889 / 1000000000) x162 := by
    exact bounds_log hx161 (by norm_num) (by simpa only [div_one] using reflection_log_4902.1) (by simpa only [div_one] using reflection_log_4902.2)
  let x163 : ℝ := x160*x162
  have hx163 : Bounds (24322499251 / 250000000000) (48644999049 / 500000000000) x163 := by
    apply bounds_mul hx160 hx162 <;> norm_num
  let x164 : ℝ := -(46543 / 500000)
  have hx164 : Bounds (-46543 / 500000) (-46543 / 500000) x164 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((46543 / 500000) : ℝ))
  let x165 : ℝ := (1 / 1)+x164
  have hx165 : Bounds (453457 / 500000) (453457 / 500000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx164 <;> norm_num
  let x166 : ℝ := (1 / 1)-(46543 / 500000)
  have hx166 : Bounds (453457 / 500000) (453457 / 500000) x166 := by
    exact hx165
  let x167 : ℝ := -(46543 / 500000)
  have hx167 : Bounds (-46543 / 500000) (-46543 / 500000) x167 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((46543 / 500000) : ℝ))
  let x168 : ℝ := (1 / 1)+x167
  have hx168 : Bounds (453457 / 500000) (453457 / 500000) x168 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx167 <;> norm_num
  let x169 : ℝ := (1 / 1)-(46543 / 500000)
  have hx169 : Bounds (453457 / 500000) (453457 / 500000) x169 := by
    exact hx168
  let x170 : ℝ := Real.log x169
  have hx170 : Bounds (-24426913 / 250000000) (-97707651 / 1000000000) x170 := by
    exact bounds_log hx169 (by norm_num) (by simpa only [div_one] using reflection_log_4903.1) (by simpa only [div_one] using reflection_log_4903.2)
  let x171 : ℝ := x166*x170
  have hx171 : Bounds (-44306218753 / 500000000000) (-88612436599 / 1000000000000) x171 := by
    apply bounds_mul hx166 hx170 <;> norm_num
  let x172 : ℝ := x163+x171
  have hx172 : Bounds (4338779749 / 500000000000) (8677561499 / 1000000000000) x172 := by
    apply bounds_add hx163 hx171 <;> norm_num
  let x173 : ℝ := (2 / 1)⁻¹
  have hx173 : Bounds (1 / 2) (1 / 2) x173 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x174 : ℝ := x172*x173
  have hx174 : Bounds (4338779749 / 1000000000000) (17355123 / 4000000000) x174 := by
    apply bounds_mul hx172 hx173 <;> norm_num
  let x175 : ℝ := x172/(2 / 1)
  have hx175 : Bounds (4338779749 / 1000000000000) (17355123 / 4000000000) x175 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx174
  let x176 : ℝ := -x175
  have hx176 : Bounds (-17355123 / 4000000000) (-4338779749 / 1000000000000) x176 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx175
  let x177 : ℝ := x159+x176
  have hx177 : Bounds (2755233597 / 4000000000) (688808401251 / 1000000000000) x177 := by
    apply bounds_add hx159 hx176 <;> norm_num
  let x178 : ℝ := x159-x175
  have hx178 : Bounds (2755233597 / 4000000000) (688808401251 / 1000000000000) x178 := by
    exact hx177
  let x179 : ℝ := biasE (46543 / 500000)
  have hx179 : Bounds (2755233597 / 4000000000) (688808401251 / 1000000000000) x179 := by
    simpa +zetaDelta only [biasE, div_one] using hx178
  let x180 : ℝ := biasE c
  have hx180 : Bounds (172196584797 / 250000000000) (688808401251 / 1000000000000) x180 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx158.1 hx179.2
  let x181 : ℝ := Real.log (2 / 1)
  have hx181 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x181 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x182 : ℝ := c*c
  have hx182 : Bounds (2166250849 / 250000000000) (2177248921 / 250000000000) x182 := by
    apply bounds_mul hc hc <;> norm_num
  let x183 : ℝ := -x182
  have hx183 : Bounds (-2177248921 / 250000000000) (-2166250849 / 250000000000) x183 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx182
  let x184 : ℝ := (1 / 1)+x183
  have hx184 : Bounds (247822751079 / 250000000000) (247833749151 / 250000000000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx183 <;> norm_num
  let x185 : ℝ := (1 / 1)-x182
  have hx185 : Bounds (247822751079 / 250000000000) (247833749151 / 250000000000) x185 := by
    exact hx184
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (-8747141 / 1000000000) (-4351381 / 500000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_4906.1) (by simpa only [div_one] using reflection_log_4907.2)
  let x187 : ℝ := (2 / 1)⁻¹
  have hx187 : Bounds (1 / 2) (1 / 2) x187 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x188 : ℝ := x186*x187
  have hx188 : Bounds (-8747141 / 2000000000) (-4351381 / 1000000000) x188 := by
    apply bounds_mul hx186 hx187 <;> norm_num
  let x189 : ℝ := x186/(2 / 1)
  have hx189 : Bounds (-8747141 / 2000000000) (-4351381 / 1000000000) x189 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx188
  let x190 : ℝ := -x189
  have hx190 : Bounds (4351381 / 1000000000) (8747141 / 2000000000) x190 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx189
  let x191 : ℝ := x181+x190
  have hx191 : Bounds (697498561 / 1000000000) (1395041503 / 2000000000) x191 := by
    apply bounds_add hx181 hx190 <;> norm_num
  let x192 : ℝ := x181-x189
  have hx192 : Bounds (697498561 / 1000000000) (1395041503 / 2000000000) x192 := by
    exact hx191
  let x193 : ℝ := c*(1 / 1)
  have hx193 : Bounds (46543 / 500000) (46661 / 500000) x193 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x194 : ℝ := c*x193
  have hx194 : Bounds (2166250849 / 250000000000) (2177248921 / 250000000000) x194 := by
    apply bounds_mul hc hx193 <;> norm_num
  let x195 : ℝ := c^2
  have hx195 : Bounds (2166250849 / 250000000000) (2177248921 / 250000000000) x195 := by
    (convert hx194 using 1; ring)
  let x196 : ℝ := -x195
  have hx196 : Bounds (-2177248921 / 250000000000) (-2166250849 / 250000000000) x196 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx195
  let x197 : ℝ := (1 / 1)+x196
  have hx197 : Bounds (247822751079 / 250000000000) (247833749151 / 250000000000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx196 <;> norm_num
  let x198 : ℝ := (1 / 1)-x195
  have hx198 : Bounds (247822751079 / 250000000000) (247833749151 / 250000000000) x198 := by
    exact hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (546543 / 500000) (546661 / 500000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-46661 / 500000) (-46543 / 500000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (453339 / 500000) (453457 / 500000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (453339 / 500000) (453457 / 500000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (55132019133 / 50000000000) (1102927389879 / 1000000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (30132019133 / 25000000000) (602927389879 / 500000000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (30132019133 / 25000000000) (602927389879 / 500000000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (9335627 / 50000000) (187188677 / 1000000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_4908.1) (by simpa only [div_one] using reflection_log_4909.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (9335627 / 100000000) (187188677 / 2000000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (9335627 / 100000000) (187188677 / 2000000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (1 / 1)+a
  have hx210 : Bounds (2963 / 2500) (11853 / 10000) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) ha <;> norm_num
  let x211 : ℝ := -a
  have hx211 : Bounds (-1853 / 10000) (-463 / 2500) x211 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg ha
  let x212 : ℝ := (1 / 1)+x211
  have hx212 : Bounds (8147 / 10000) (2037 / 2500) x212 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx211 <;> norm_num
  let x213 : ℝ := (1 / 1)-a
  have hx213 : Bounds (8147 / 10000) (2037 / 2500) x213 := by
    exact hx212
  let x214 : ℝ := x213⁻¹
  have hx214 : Bounds (19176485027 / 15625000000) (1227445685529 / 1000000000000) x214 := by
    apply bounds_inv hx213 <;> norm_num
  let x215 : ℝ := x210*x214
  have hx215 : Bounds (11363985027 / 7812500000) (727445685529 / 500000000000) x215 := by
    apply bounds_mul hx210 hx214 <;> norm_num
  let x216 : ℝ := x210/x213
  have hx216 : Bounds (11363985027 / 7812500000) (727445685529 / 500000000000) x216 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx215
  let x217 : ℝ := Real.log x216
  have hx217 : Bounds (374724131 / 1000000000) (374931239 / 1000000000) x217 := by
    exact bounds_log hx216 (by norm_num) (by simpa only [div_one] using reflection_log_4910.1) (by simpa only [div_one] using reflection_log_4911.2)
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (374724131 / 2000000000) (374931239 / 2000000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (374724131 / 2000000000) (374931239 / 2000000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := (2 / 1)*x192
  have hx221 : Bounds (697498561 / 500000000) (1395041503 / 1000000000) x221 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x222 : ℝ := c*(1 / 1)
  have hx222 : Bounds (46543 / 500000) (46661 / 500000) x222 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x223 : ℝ := c*x222
  have hx223 : Bounds (2166250849 / 250000000000) (2177248921 / 250000000000) x223 := by
    apply bounds_mul hc hx222 <;> norm_num
  let x224 : ℝ := c^2
  have hx224 : Bounds (2166250849 / 250000000000) (2177248921 / 250000000000) x224 := by
    (convert hx223 using 1; ring)
  let x225 : ℝ := -x224
  have hx225 : Bounds (-2177248921 / 250000000000) (-2166250849 / 250000000000) x225 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx224
  let x226 : ℝ := x221+x225
  have hx226 : Bounds (346572031579 / 250000000000) (346594124901 / 250000000000) x226 := by
    apply bounds_add hx221 hx225 <;> norm_num
  let x227 : ℝ := x221-x224
  have hx227 : Bounds (346572031579 / 250000000000) (346594124901 / 250000000000) x227 := by
    exact hx226
  let x228 : ℝ := x180*x227
  have hx228 : Bounds (1864953757 / 1953125000) (38197911209 / 40000000000) x228 := by
    apply bounds_mul hx180 hx227 <;> norm_num
  let x229 : ℝ := (2 / 1)*x90
  have hx229 : Bounds (342256668717 / 250000000000) (136904543697 / 100000000000) x229 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x230 : ℝ := x198*(1 / 1)
  have hx230 : Bounds (247822751079 / 250000000000) (247833749151 / 250000000000) x230 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x231 : ℝ := x198*x230
  have hx231 : Bounds (982657855237 / 1000000000000) (245686268873 / 250000000000) x231 := by
    apply bounds_mul hx198 hx230 <;> norm_num
  let x232 : ℝ := x198^2
  have hx232 : Bounds (982657855237 / 1000000000000) (245686268873 / 250000000000) x232 := by
    (convert hx231 using 1; ring)
  let x233 : ℝ := x229*x232
  have hx233 : Bounds (168160602011 / 125000000000) (336355665327 / 250000000000) x233 := by
    apply bounds_mul hx229 hx232 <;> norm_num
  let x234 : ℝ := x192*(1 / 1)
  have hx234 : Bounds (697498561 / 1000000000) (1395041503 / 2000000000) x234 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x235 : ℝ := x192*x234
  have hx235 : Bounds (486504242597 / 1000000000000) (243267599387 / 500000000000) x235 := by
    apply bounds_mul hx192 hx234 <;> norm_num
  let x236 : ℝ := x192*x235
  have hx236 : Bounds (339336009131 / 1000000000000) (339368397481 / 1000000000000) x236 := by
    apply bounds_mul hx192 hx235 <;> norm_num
  let x237 : ℝ := x192^3
  have hx237 : Bounds (339336009131 / 1000000000000) (339368397481 / 1000000000000) x237 := by
    (convert hx236 using 1; ring)
  let x238 : ℝ := x233*x237
  have hx238 : Bounds (91300716127 / 200000000000) (456593932503 / 1000000000000) x238 := by
    apply bounds_mul hx233 hx237 <;> norm_num
  let x239 : ℝ := x238⁻¹
  have hx239 : Bounds (109506492401 / 50000000000) (109528166089 / 50000000000) x239 := by
    apply bounds_inv hx238 <;> norm_num
  let x240 : ℝ := x228*x239
  have hx240 : Bounds (2091259334851 / 1000000000000) (2091873581577 / 1000000000000) x240 := by
    apply bounds_mul hx228 hx239 <;> norm_num
  let x241 : ℝ := x228/x238
  have hx241 : Bounds (2091259334851 / 1000000000000) (2091873581577 / 1000000000000) x241 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx240
  let x242 : ℝ := -x209
  have hx242 : Bounds (-187188677 / 2000000000) (-9335627 / 100000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x243 : ℝ := (2 / 1)*x192
  have hx243 : Bounds (697498561 / 500000000) (1395041503 / 1000000000) x243 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x244 : ℝ := c*(1 / 1)
  have hx244 : Bounds (46543 / 500000) (46661 / 500000) x244 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x245 : ℝ := c*x244
  have hx245 : Bounds (2166250849 / 250000000000) (2177248921 / 250000000000) x245 := by
    apply bounds_mul hc hx244 <;> norm_num
  let x246 : ℝ := c^2
  have hx246 : Bounds (2166250849 / 250000000000) (2177248921 / 250000000000) x246 := by
    (convert hx245 using 1; ring)
  let x247 : ℝ := -x246
  have hx247 : Bounds (-2177248921 / 250000000000) (-2166250849 / 250000000000) x247 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx246
  let x248 : ℝ := x243+x247
  have hx248 : Bounds (346572031579 / 250000000000) (346594124901 / 250000000000) x248 := by
    apply bounds_add hx243 hx247 <;> norm_num
  let x249 : ℝ := x243-x246
  have hx249 : Bounds (346572031579 / 250000000000) (346594124901 / 250000000000) x249 := by
    exact hx248
  let x250 : ℝ := x242*x249
  have hx250 : Bounds (-129756991393 / 1000000000000) (-64709344309 / 500000000000) x250 := by
    apply bounds_mul hx242 hx249 <;> norm_num
  let x251 : ℝ := x198⁻¹
  have hx251 : Bounds (504370370977 / 500000000000) (1008785508641 / 1000000000000) x251 := by
    apply bounds_inv hx198 <;> norm_num
  let x252 : ℝ := c*x251
  have hx252 : Bounds (18779928141 / 200000000000) (47070940619 / 500000000000) x252 := by
    apply bounds_mul hc hx251 <;> norm_num
  let x253 : ℝ := c/x198
  have hx253 : Bounds (18779928141 / 200000000000) (47070940619 / 500000000000) x253 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx252
  let x254 : ℝ := (2 / 1)*x253
  have hx254 : Bounds (18779928141 / 100000000000) (47070940619 / 250000000000) x254 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx253 <;> norm_num
  let x255 : ℝ := (2 / 1)*c
  have hx255 : Bounds (46543 / 250000) (46661 / 250000) x255 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hc <;> norm_num
  let x256 : ℝ := -x255
  have hx256 : Bounds (-46661 / 250000) (-46543 / 250000) x256 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx255
  let x257 : ℝ := x254+x256
  have hx257 : Bounds (115528141 / 100000000000) (527940619 / 250000000000) x257 := by
    apply bounds_add hx254 hx256 <;> norm_num
  let x258 : ℝ := x254-x255
  have hx258 : Bounds (115528141 / 100000000000) (527940619 / 250000000000) x258 := by
    exact hx257
  let x259 : ℝ := x180*x258
  have hx259 : Bounds (795742053 / 1000000000000) (290919947 / 200000000000) x259 := by
    apply bounds_mul hx180 hx258 <;> norm_num
  let x260 : ℝ := x250+x259
  have hx260 : Bounds (-6448062467 / 50000000000) (-127964088883 / 1000000000000) x260 := by
    apply bounds_add hx250 hx259 <;> norm_num
  let x261 : ℝ := (2 / 1)*x90
  have hx261 : Bounds (342256668717 / 250000000000) (136904543697 / 100000000000) x261 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x262 : ℝ := x198*(1 / 1)
  have hx262 : Bounds (247822751079 / 250000000000) (247833749151 / 250000000000) x262 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x263 : ℝ := x198*x262
  have hx263 : Bounds (982657855237 / 1000000000000) (245686268873 / 250000000000) x263 := by
    apply bounds_mul hx198 hx262 <;> norm_num
  let x264 : ℝ := x198^2
  have hx264 : Bounds (982657855237 / 1000000000000) (245686268873 / 250000000000) x264 := by
    (convert hx263 using 1; ring)
  let x265 : ℝ := x261*x264
  have hx265 : Bounds (168160602011 / 125000000000) (336355665327 / 250000000000) x265 := by
    apply bounds_mul hx261 hx264 <;> norm_num
  let x266 : ℝ := x192*(1 / 1)
  have hx266 : Bounds (697498561 / 1000000000) (1395041503 / 2000000000) x266 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x267 : ℝ := x192*x266
  have hx267 : Bounds (486504242597 / 1000000000000) (243267599387 / 500000000000) x267 := by
    apply bounds_mul hx192 hx266 <;> norm_num
  let x268 : ℝ := x192*x267
  have hx268 : Bounds (339336009131 / 1000000000000) (339368397481 / 1000000000000) x268 := by
    apply bounds_mul hx192 hx267 <;> norm_num
  let x269 : ℝ := x192^3
  have hx269 : Bounds (339336009131 / 1000000000000) (339368397481 / 1000000000000) x269 := by
    (convert hx268 using 1; ring)
  let x270 : ℝ := x265*x269
  have hx270 : Bounds (91300716127 / 200000000000) (456593932503 / 1000000000000) x270 := by
    apply bounds_mul hx265 hx269 <;> norm_num
  let x271 : ℝ := x270⁻¹
  have hx271 : Bounds (109506492401 / 50000000000) (109528166089 / 50000000000) x271 := by
    apply bounds_inv hx270 <;> norm_num
  let x272 : ℝ := x260*x271
  have hx272 : Bounds (-17656111421 / 62500000000) (-280257970537 / 1000000000000) x272 := by
    apply bounds_mul hx260 hx271 <;> norm_num
  let x273 : ℝ := x260/x270
  have hx273 : Bounds (-17656111421 / 62500000000) (-280257970537 / 1000000000000) x273 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx272
  let x274 : ℝ := (4 / 1)*c
  have hx274 : Bounds (46543 / 125000) (46661 / 125000) x274 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hc <;> norm_num
  let x275 : ℝ := x198⁻¹
  have hx275 : Bounds (504370370977 / 500000000000) (1008785508641 / 1000000000000) x275 := by
    apply bounds_inv hx198 <;> norm_num
  let x276 : ℝ := x274*x275
  have hx276 : Bounds (187799281411 / 500000000000) (7531350499 / 20000000000) x276 := by
    apply bounds_mul hx274 hx275 <;> norm_num
  let x277 : ℝ := x274/x198
  have hx277 : Bounds (187799281411 / 500000000000) (7531350499 / 20000000000) x277 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx276
  let x278 : ℝ := (3 / 1)*c
  have hx278 : Bounds (139629 / 500000) (139983 / 500000) x278 := by
    apply bounds_mul (bounds_const ((3 / 1) : ℝ)) hc <;> norm_num
  let x279 : ℝ := x198*x192
  have hx279 : Bounds (345712024521 / 500000000000) (34573836591 / 50000000000) x279 := by
    apply bounds_mul hx198 hx192 <;> norm_num
  let x280 : ℝ := x279⁻¹
  have hx280 : Bounds (723090130139 / 500000000000) (361572612851 / 250000000000) x280 := by
    apply bounds_inv hx279 <;> norm_num
  let x281 : ℝ := x278*x280
  have hx281 : Bounds (100964351781 / 250000000000) (202456076259 / 500000000000) x281 := by
    apply bounds_mul hx278 hx280 <;> norm_num
  let x282 : ℝ := x278/x279
  have hx282 : Bounds (100964351781 / 250000000000) (202456076259 / 500000000000) x282 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx281
  let x283 : ℝ := -x282
  have hx283 : Bounds (-202456076259 / 500000000000) (-100964351781 / 250000000000) x283 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx282
  let x284 : ℝ := x277+x283
  have hx284 : Bounds (-458024839 / 15625000000) (-13644941087 / 500000000000) x284 := by
    apply bounds_add hx277 hx283 <;> norm_num
  let x285 : ℝ := x277-x282
  have hx285 : Bounds (-458024839 / 15625000000) (-13644941087 / 500000000000) x285 := by
    exact hx284
  let x286 : ℝ := x241*x285
  have hx286 : Bounds (-61320323867 / 1000000000000) (-57070220843 / 1000000000000) x286 := by
    apply bounds_mul hx241 hx285 <;> norm_num
  let x287 : ℝ := x273+x286
  have hx287 : Bounds (-343818106603 / 1000000000000) (-16866409569 / 50000000000) x287 := by
    apply bounds_add hx273 hx286 <;> norm_num
  let x288 : ℝ := (2 / 1)*x192
  have hx288 : Bounds (697498561 / 500000000) (1395041503 / 1000000000) x288 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x289 : ℝ := c*(1 / 1)
  have hx289 : Bounds (46543 / 500000) (46661 / 500000) x289 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x290 : ℝ := c*x289
  have hx290 : Bounds (2166250849 / 250000000000) (2177248921 / 250000000000) x290 := by
    apply bounds_mul hc hx289 <;> norm_num
  let x291 : ℝ := c^2
  have hx291 : Bounds (2166250849 / 250000000000) (2177248921 / 250000000000) x291 := by
    (convert hx290 using 1; ring)
  let x292 : ℝ := -x291
  have hx292 : Bounds (-2177248921 / 250000000000) (-2166250849 / 250000000000) x292 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx291
  let x293 : ℝ := x288+x292
  have hx293 : Bounds (346572031579 / 250000000000) (346594124901 / 250000000000) x293 := by
    apply bounds_add hx288 hx292 <;> norm_num
  let x294 : ℝ := x288-x291
  have hx294 : Bounds (346572031579 / 250000000000) (346594124901 / 250000000000) x294 := by
    exact hx293
  let x295 : ℝ := c*x294
  have hx295 : Bounds (64522008263 / 500000000000) (129379427697 / 1000000000000) x295 := by
    apply bounds_mul hc hx294 <;> norm_num
  let x296 : ℝ := x198*(1 / 1)
  have hx296 : Bounds (247822751079 / 250000000000) (247833749151 / 250000000000) x296 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x297 : ℝ := x198*x296
  have hx297 : Bounds (982657855237 / 1000000000000) (245686268873 / 250000000000) x297 := by
    apply bounds_mul hx198 hx296 <;> norm_num
  let x298 : ℝ := x198^2
  have hx298 : Bounds (982657855237 / 1000000000000) (245686268873 / 250000000000) x298 := by
    (convert hx297 using 1; ring)
  let x299 : ℝ := x192*(1 / 1)
  have hx299 : Bounds (697498561 / 1000000000) (1395041503 / 2000000000) x299 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x300 : ℝ := x192*x299
  have hx300 : Bounds (486504242597 / 1000000000000) (243267599387 / 500000000000) x300 := by
    apply bounds_mul hx192 hx299 <;> norm_num
  let x301 : ℝ := x192^2
  have hx301 : Bounds (486504242597 / 1000000000000) (243267599387 / 500000000000) x301 := by
    (convert hx300 using 1; ring)
  let x302 : ℝ := x298*x301
  have hx302 : Bounds (239033607797 / 500000000000) (478140070649 / 1000000000000) x302 := by
    apply bounds_mul hx298 hx301 <;> norm_num
  let x303 : ℝ := x302⁻¹
  have hx303 : Bounds (32678708519 / 15625000000) (2091756069819 / 1000000000000) x303 := by
    apply bounds_inv hx302 <;> norm_num
  let x304 : ℝ := x295*x303
  have hx304 : Bounds (269887475339 / 1000000000000) (54126040639 / 200000000000) x304 := by
    apply bounds_mul hx295 hx303 <;> norm_num
  let x305 : ℝ := x295/x302
  have hx305 : Bounds (269887475339 / 1000000000000) (54126040639 / 200000000000) x305 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx304
  let x306 : ℝ := c*x220
  have hx306 : Bounds (17440785229 / 1000000000000) (17494666543 / 1000000000000) x306 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x307 : ℝ := x180+x306
  have hx307 : Bounds (706227124417 / 1000000000000) (353151533897 / 500000000000) x307 := by
    apply bounds_add hx180 hx306 <;> norm_num
  let x308 : ℝ := x307*(1 / 1)
  have hx308 : Bounds (706227124417 / 1000000000000) (353151533897 / 500000000000) x308 := by
    apply bounds_mul hx307 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x309 : ℝ := x307*x308
  have hx309 : Bounds (249378375631 / 500000000000) (62358002947 / 125000000000) x309 := by
    apply bounds_mul hx307 hx308 <;> norm_num
  let x310 : ℝ := x307^2
  have hx310 : Bounds (249378375631 / 500000000000) (62358002947 / 125000000000) x310 := by
    (convert hx309 using 1; ring)
  let x311 : ℝ := x287*x310
  have hx311 : Bounds (-171518484039 / 1000000000000) (-168244712841 / 1000000000000) x311 := by
    apply bounds_mul hx287 hx310 <;> norm_num
  let x312 : ℝ := (2 / 1)*x241
  have hx312 : Bounds (2091259334851 / 500000000000) (2091873581577 / 500000000000) x312 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx241 <;> norm_num
  let x313 : ℝ := c*x220
  have hx313 : Bounds (17440785229 / 1000000000000) (17494666543 / 1000000000000) x313 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x314 : ℝ := x180+x313
  have hx314 : Bounds (706227124417 / 1000000000000) (353151533897 / 500000000000) x314 := by
    apply bounds_add hx180 hx313 <;> norm_num
  let x315 : ℝ := x312*x314
  have hx315 : Bounds (738452033231 / 250000000000) (2954993456211 / 1000000000000) x315 := by
    apply bounds_mul hx312 hx314 <;> norm_num
  let x316 : ℝ := -x209
  have hx316 : Bounds (-187188677 / 2000000000) (-9335627 / 100000000) x316 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x317 : ℝ := x220+x316
  have hx317 : Bounds (93767727 / 1000000000) (188218699 / 2000000000) x317 := by
    apply bounds_add hx220 hx316 <;> norm_num
  let x318 : ℝ := x220-x209
  have hx318 : Bounds (93767727 / 1000000000) (188218699 / 2000000000) x318 := by
    exact hx317
  let x319 : ℝ := x315*x318
  have hx319 : Bounds (138485937309 / 500000000000) (278092511941 / 1000000000000) x319 := by
    apply bounds_mul hx315 hx318 <;> norm_num
  let x320 : ℝ := x311+x319
  have hx320 : Bounds (105453390579 / 1000000000000) (1098477991 / 10000000000) x320 := by
    apply bounds_add hx311 hx319 <;> norm_num
  let x321 : ℝ := a*(1 / 1)
  have hx321 : Bounds (463 / 2500) (1853 / 10000) x321 := by
    apply bounds_mul ha (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x322 : ℝ := a*x321
  have hx322 : Bounds (214369 / 6250000) (3433609 / 100000000) x322 := by
    apply bounds_mul ha hx321 <;> norm_num
  let x323 : ℝ := a^2
  have hx323 : Bounds (214369 / 6250000) (3433609 / 100000000) x323 := by
    (convert hx322 using 1; ring)
  let x324 : ℝ := -x323
  have hx324 : Bounds (-3433609 / 100000000) (-214369 / 6250000) x324 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx323
  let x325 : ℝ := (1 / 1)+x324
  have hx325 : Bounds (96566391 / 100000000) (6035631 / 6250000) x325 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx324 <;> norm_num
  let x326 : ℝ := (1 / 1)-x323
  have hx326 : Bounds (96566391 / 100000000) (6035631 / 6250000) x326 := by
    exact hx325
  let x327 : ℝ := x326⁻¹
  have hx327 : Bounds (258879311873 / 250000000000) (1035556977583 / 1000000000000) x327 := by
    apply bounds_inv hx326 <;> norm_num
  let x328 : ℝ := (1 / 1)*x327
  have hx328 : Bounds (258879311873 / 250000000000) (1035556977583 / 1000000000000) x328 := by
    apply bounds_mul (bounds_const ((1 / 1) : ℝ)) hx327 <;> norm_num
  let x329 : ℝ := (1 / 1)/x326
  have hx329 : Bounds (258879311873 / 250000000000) (1035556977583 / 1000000000000) x329 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx328
  let x330 : ℝ := x329*x305
  have hx330 : Bounds (55894627119 / 200000000000) (4378953051 / 15625000000) x330 := by
    apply bounds_mul hx329 hx305 <;> norm_num
  let x331 : ℝ := x320+x330
  have hx331 : Bounds (192463263087 / 500000000000) (97525198591 / 250000000000) x331 := by
    apply bounds_add hx320 hx330 <;> norm_num
  let x332 : ℝ := x180*(1 / 1)
  have hx332 : Bounds (172196584797 / 250000000000) (688808401251 / 1000000000000) x332 := by
    apply bounds_mul hx180 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x333 : ℝ := x180*x332
  have hx333 : Bounds (118606655263 / 250000000000) (237228506817 / 500000000000) x333 := by
    apply bounds_mul hx180 hx332 <;> norm_num
  let x334 : ℝ := x180^2
  have hx334 : Bounds (118606655263 / 250000000000) (237228506817 / 500000000000) x334 := by
    (convert hx333 using 1; ring)
  let x335 : ℝ := x331*x334
  have hx335 : Bounds (91309695583 / 500000000000) (185086057911 / 1000000000000) x335 := by
    apply bounds_mul hx331 hx334 <;> norm_num
  let x336 : ℝ := x90*x192
  have hx336 : Bounds (95489413569 / 200000000000) (477468801017 / 1000000000000) x336 := by
    apply bounds_mul hx90 hx192 <;> norm_num
  let x337 : ℝ := x336⁻¹
  have hx337 : Bounds (2094377680531 / 1000000000000) (418894603129 / 200000000000) x337 := by
    apply bounds_inv hx336 <;> norm_num
  let x338 : ℝ := x335*x337
  have hx338 : Bounds (38247397689 / 100000000000) (387657753867 / 1000000000000) x338 := by
    apply bounds_mul hx335 hx337 <;> norm_num
  let x339 : ℝ := x335/x336
  have hx339 : Bounds (38247397689 / 100000000000) (387657753867 / 1000000000000) x339 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx338
  have hu : x339 < (28590672898290095241828587 / 72857683136322000000000000) := lt_of_le_of_lt hx339.2 (by norm_num)
  simpa +zetaDelta only [ScFormula,Kprime,K,Mprime,SmallMean.A,biasB,div_one,pow_two] using hu

open GeneralCK.Reflection
/-- Uniform derivative enclosure including input boxes with z=0. -/
theorem derivative_bound_352 {a z s : ℝ}
    (ha : a ∈ Set.Icc ((463 / 2500):ℝ) ((1853 / 10000)))
    (hz : z ∈ Set.Icc (0:ℝ) (1/1000))
    (hs : s ∈ Set.Ioo (a*(1-z)/2) (a*(1+z)/2)) :
    P a ((biasE a+biasE (a*z))/2) s ≤ (28590672898290095241828587 / 72857683136322000000000000) := by
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
  have hsl : (462537 / 5000000) ≤ s := by
    have h := mul_le_mul ha.1 (show (999/1000:ℝ) ≤ 1-z by linarith [hz.2])
      (by norm_num : (0:ℝ) ≤ 999/1000) ha0.le
    nlinarith [hs.1]
  have hsu : s ≤ (1854853 / 20000000) := by
    have h := mul_le_mul ha.2 (show 1+z ≤ (1001/1000:ℝ) by linarith [hz.2])
      (by linarith [hz.1] : 0 ≤ 1+z) (by norm_num : (0:ℝ) ≤ (1853 / 10000))
    nlinarith [hs.2]
  have hy := div_pos he hs0
  have hc := biasContact_mem hy
  have heq : biasE (biasContact (((biasE a+biasE (a*z))/2)/s)) =
      (((biasE a+biasE (a*z))/2)/s)*biasContact (((biasE a+biasE (a*z))/2)/s) := by
    exact (div_eq_iff hc.1.ne').mp (biasR_biasContact hy)
  have hb := derivative_leaf_352 a z s _ ha hz ⟨hsl,hsu⟩ hc.1.le hc.2.le heq
  rw [P_eq_formula ha0 ha1 he hs0]
  exact hb.le

/-- Checked low-ratio strip: includes arbitrarily small positive z. -/
theorem curvature_leaf_352 {a z : ℝ}
    (ha : a ∈ Set.Icc ((463 / 2500):ℝ) ((1853 / 10000)))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < curvature a (a*z) := by
  have ha0 : 0 < a := by linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  apply curvature_pos_of_derivative_bound ha0 ha1 hz.1 (by linarith [hz.2])
    (fun s hs => derivative_bound_352 ha ⟨hz.1.le,hz.2⟩ hs) (M := (28590672898290095241828587 / 72857683136322000000000000))
  exact lt_of_lt_of_le (by norm_num : (28590672898290095241828587 / 72857683136322000000000000) < 2*((463 / 2500):ℝ)/(1-((463 / 2500):ℝ)^2)^2)
    (base_mono (by norm_num) ha.1 ha1)

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Cell0353 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
theorem derivative_leaf_353 (a z s c : ℝ)
    (ha : Bounds (1853 / 10000) (927 / 5000) a) (hz : Bounds 0 (1/1000) z)
    (hs : Bounds (1851147 / 20000000) (927927 / 10000000) s) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (heq : biasE c = (((biasE a+biasE (a*z))/2)/s)*c) :
    ScFormula c a ((biasE a+biasE (a*z))/2)*(biasE c)^2 /
      (((biasE a+biasE (a*z))/2)*biasB c) < (1830756905691727590892290793 / 4662533935382440500000000000) := by
  let x0 : ℝ := Real.log (2 / 1)
  have hx0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x0 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x1 : ℝ := (1 / 1)+(927 / 5000)
  have hx1 : Bounds (5927 / 5000) (5927 / 5000) x1 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((927 / 5000) : ℝ)) <;> norm_num
  let x2 : ℝ := (1 / 1)+(927 / 5000)
  have hx2 : Bounds (5927 / 5000) (5927 / 5000) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((927 / 5000) : ℝ)) <;> norm_num
  let x3 : ℝ := Real.log x2
  have hx3 : Bounds (17008027 / 100000000) (170080271 / 1000000000) x3 := by
    exact bounds_log hx2 (by norm_num) (by simpa only [div_one] using reflection_log_4912.1) (by simpa only [div_one] using reflection_log_4912.2)
  let x4 : ℝ := x1*x3
  have hx4 : Bounds (100806576029 / 500000000000) (50403288311 / 250000000000) x4 := by
    apply bounds_mul hx1 hx3 <;> norm_num
  let x5 : ℝ := -(927 / 5000)
  have hx5 : Bounds (-927 / 5000) (-927 / 5000) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((927 / 5000) : ℝ))
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (4073 / 5000) (4073 / 5000) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-(927 / 5000)
  have hx7 : Bounds (4073 / 5000) (4073 / 5000) x7 := by
    exact hx6
  let x8 : ℝ := -(927 / 5000)
  have hx8 : Bounds (-927 / 5000) (-927 / 5000) x8 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((927 / 5000) : ℝ))
  let x9 : ℝ := (1 / 1)+x8
  have hx9 : Bounds (4073 / 5000) (4073 / 5000) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx8 <;> norm_num
  let x10 : ℝ := (1 / 1)-(927 / 5000)
  have hx10 : Bounds (4073 / 5000) (4073 / 5000) x10 := by
    exact hx9
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (-51264521 / 250000000) (-205058083 / 1000000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_4913.1) (by simpa only [div_one] using reflection_log_4913.2)
  let x12 : ℝ := x7*x11
  have hx12 : Bounds (-167040315227 / 1000000000000) (-167040314411 / 1000000000000) x12 := by
    apply bounds_mul hx7 hx11 <;> norm_num
  let x13 : ℝ := x4+x12
  have hx13 : Bounds (34572836831 / 1000000000000) (34572838833 / 1000000000000) x13 := by
    apply bounds_add hx4 hx12 <;> norm_num
  let x14 : ℝ := (2 / 1)⁻¹
  have hx14 : Bounds (1 / 2) (1 / 2) x14 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x15 : ℝ := x13*x14
  have hx15 : Bounds (3457283683 / 200000000000) (17286419417 / 1000000000000) x15 := by
    apply bounds_mul hx13 hx14 <;> norm_num
  let x16 : ℝ := x13/(2 / 1)
  have hx16 : Bounds (3457283683 / 200000000000) (17286419417 / 1000000000000) x16 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx15
  let x17 : ℝ := -x16
  have hx17 : Bounds (-17286419417 / 1000000000000) (-3457283683 / 200000000000) x17 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx16
  let x18 : ℝ := x0+x17
  have hx18 : Bounds (675860760583 / 1000000000000) (135172152517 / 200000000000) x18 := by
    apply bounds_add hx0 hx17 <;> norm_num
  let x19 : ℝ := x0-x16
  have hx19 : Bounds (675860760583 / 1000000000000) (135172152517 / 200000000000) x19 := by
    exact hx18
  let x20 : ℝ := biasE (927 / 5000)
  have hx20 : Bounds (675860760583 / 1000000000000) (135172152517 / 200000000000) x20 := by
    simpa +zetaDelta only [biasE, div_one] using hx19
  let x21 : ℝ := Real.log (2 / 1)
  have hx21 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x21 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x22 : ℝ := (1 / 1)+(1853 / 10000)
  have hx22 : Bounds (11853 / 10000) (11853 / 10000) x22 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1853 / 10000) : ℝ)) <;> norm_num
  let x23 : ℝ := (1 / 1)+(1853 / 10000)
  have hx23 : Bounds (11853 / 10000) (11853 / 10000) x23 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1853 / 10000) : ℝ)) <;> norm_num
  let x24 : ℝ := Real.log x23
  have hx24 : Bounds (169995907 / 1000000000) (42498977 / 250000000) x24 := by
    exact bounds_log hx23 (by norm_num) (by simpa only [div_one] using reflection_log_4898.1) (by simpa only [div_one] using reflection_log_4898.2)
  let x25 : ℝ := x22*x24
  have hx25 : Bounds (201496148567 / 1000000000000) (201496149753 / 1000000000000) x25 := by
    apply bounds_mul hx22 hx24 <;> norm_num
  let x26 : ℝ := -(1853 / 10000)
  have hx26 : Bounds (-1853 / 10000) (-1853 / 10000) x26 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1853 / 10000) : ℝ))
  let x27 : ℝ := (1 / 1)+x26
  have hx27 : Bounds (8147 / 10000) (8147 / 10000) x27 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx26 <;> norm_num
  let x28 : ℝ := (1 / 1)-(1853 / 10000)
  have hx28 : Bounds (8147 / 10000) (8147 / 10000) x28 := by
    exact hx27
  let x29 : ℝ := -(1853 / 10000)
  have hx29 : Bounds (-1853 / 10000) (-1853 / 10000) x29 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1853 / 10000) : ℝ))
  let x30 : ℝ := (1 / 1)+x29
  have hx30 : Bounds (8147 / 10000) (8147 / 10000) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx29 <;> norm_num
  let x31 : ℝ := (1 / 1)-(1853 / 10000)
  have hx31 : Bounds (8147 / 10000) (8147 / 10000) x31 := by
    exact hx30
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (-51233833 / 250000000) (-204935331 / 1000000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_4899.1) (by simpa only [div_one] using reflection_log_4899.2)
  let x33 : ℝ := x28*x32
  have hx33 : Bounds (-166960814981 / 1000000000000) (-33392162833 / 200000000000) x33 := by
    apply bounds_mul hx28 hx32 <;> norm_num
  let x34 : ℝ := x25+x33
  have hx34 : Bounds (17267666793 / 500000000000) (8633833897 / 250000000000) x34 := by
    apply bounds_add hx25 hx33 <;> norm_num
  let x35 : ℝ := (2 / 1)⁻¹
  have hx35 : Bounds (1 / 2) (1 / 2) x35 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x36 : ℝ := x34*x35
  have hx36 : Bounds (17267666793 / 1000000000000) (8633833897 / 500000000000) x36 := by
    apply bounds_mul hx34 hx35 <;> norm_num
  let x37 : ℝ := x34/(2 / 1)
  have hx37 : Bounds (17267666793 / 1000000000000) (8633833897 / 500000000000) x37 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx36
  let x38 : ℝ := -x37
  have hx38 : Bounds (-8633833897 / 500000000000) (-17267666793 / 1000000000000) x38 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx37
  let x39 : ℝ := x21+x38
  have hx39 : Bounds (337939756103 / 500000000000) (675879514207 / 1000000000000) x39 := by
    apply bounds_add hx21 hx38 <;> norm_num
  let x40 : ℝ := x21-x37
  have hx40 : Bounds (337939756103 / 500000000000) (675879514207 / 1000000000000) x40 := by
    exact hx39
  let x41 : ℝ := biasE (1853 / 10000)
  have hx41 : Bounds (337939756103 / 500000000000) (675879514207 / 1000000000000) x41 := by
    simpa +zetaDelta only [biasE, div_one] using hx40
  let x42 : ℝ := biasE a
  have hx42 : Bounds (675860760583 / 1000000000000) (675879514207 / 1000000000000) x42 := by
    exact bounds_biasE ha (by norm_num) (by norm_num) hx20.1 hx41.2
  let x43 : ℝ := a*z
  have hx43 : Bounds (0 / 1) (927 / 5000000) x43 := by
    apply bounds_mul ha hz <;> norm_num
  let x44 : ℝ := Real.log (2 / 1)
  have hx44 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x44 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x45 : ℝ := (1 / 1)+(927 / 5000000)
  have hx45 : Bounds (5000927 / 5000000) (5000927 / 5000000) x45 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((927 / 5000000) : ℝ)) <;> norm_num
  let x46 : ℝ := (1 / 1)+(927 / 5000000)
  have hx46 : Bounds (5000927 / 5000000) (5000927 / 5000000) x46 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((927 / 5000000) : ℝ)) <;> norm_num
  let x47 : ℝ := Real.log x46
  have hx47 : Bounds (92691 / 500000000) (185383 / 1000000000) x47 := by
    exact bounds_log hx46 (by norm_num) (by simpa only [div_one] using reflection_log_4914.1) (by simpa only [div_one] using reflection_log_4914.2)
  let x48 : ℝ := x45*x47
  have hx48 : Bounds (185416369 / 1000000000000) (185417371 / 1000000000000) x48 := by
    apply bounds_mul hx45 hx47 <;> norm_num
  let x49 : ℝ := -(927 / 5000000)
  have hx49 : Bounds (-927 / 5000000) (-927 / 5000000) x49 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((927 / 5000000) : ℝ))
  let x50 : ℝ := (1 / 1)+x49
  have hx50 : Bounds (4999073 / 5000000) (4999073 / 5000000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx49 <;> norm_num
  let x51 : ℝ := (1 / 1)-(927 / 5000000)
  have hx51 : Bounds (4999073 / 5000000) (4999073 / 5000000) x51 := by
    exact hx50
  let x52 : ℝ := -(927 / 5000000)
  have hx52 : Bounds (-927 / 5000000) (-927 / 5000000) x52 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((927 / 5000000) : ℝ))
  let x53 : ℝ := (1 / 1)+x52
  have hx53 : Bounds (4999073 / 5000000) (4999073 / 5000000) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx52 <;> norm_num
  let x54 : ℝ := (1 / 1)-(927 / 5000000)
  have hx54 : Bounds (4999073 / 5000000) (4999073 / 5000000) x54 := by
    exact hx53
  let x55 : ℝ := Real.log x54
  have hx55 : Bounds (-92709 / 500000000) (-185417 / 1000000000) x55 := by
    exact bounds_log hx54 (by norm_num) (by simpa only [div_one] using reflection_log_4915.1) (by simpa only [div_one] using reflection_log_4915.2)
  let x56 : ℝ := x51*x55
  have hx56 : Bounds (-23172953 / 125000000000) (-185382623 / 1000000000000) x56 := by
    apply bounds_mul hx51 hx55 <;> norm_num
  let x57 : ℝ := x48+x56
  have hx57 : Bounds (6549 / 200000000000) (8687 / 250000000000) x57 := by
    apply bounds_add hx48 hx56 <;> norm_num
  let x58 : ℝ := (2 / 1)⁻¹
  have hx58 : Bounds (1 / 2) (1 / 2) x58 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x59 : ℝ := x57*x58
  have hx59 : Bounds (4093 / 250000000000) (8687 / 500000000000) x59 := by
    apply bounds_mul hx57 hx58 <;> norm_num
  let x60 : ℝ := x57/(2 / 1)
  have hx60 : Bounds (4093 / 250000000000) (8687 / 500000000000) x60 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx59
  let x61 : ℝ := -x60
  have hx61 : Bounds (-8687 / 500000000000) (-4093 / 250000000000) x61 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx60
  let x62 : ℝ := x44+x61
  have hx62 : Bounds (346573581313 / 500000000000) (173286791157 / 250000000000) x62 := by
    apply bounds_add hx44 hx61 <;> norm_num
  let x63 : ℝ := x44-x60
  have hx63 : Bounds (346573581313 / 500000000000) (173286791157 / 250000000000) x63 := by
    exact hx62
  let x64 : ℝ := biasE (927 / 5000000)
  have hx64 : Bounds (346573581313 / 500000000000) (173286791157 / 250000000000) x64 := by
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
  have hx86 : Bounds (346573581313 / 500000000000) (693147181 / 1000000000) x86 := by
    exact bounds_biasE hx43 (by norm_num) (by norm_num) hx64.1 hx85.2
  let x87 : ℝ := x42+x86
  have hx87 : Bounds (1369007923209 / 1000000000000) (1369026695207 / 1000000000000) x87 := by
    apply bounds_add hx42 hx86 <;> norm_num
  let x88 : ℝ := (2 / 1)⁻¹
  have hx88 : Bounds (1 / 2) (1 / 2) x88 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x89 : ℝ := x87*x88
  have hx89 : Bounds (171125990401 / 250000000000) (171128336901 / 250000000000) x89 := by
    apply bounds_mul hx87 hx88 <;> norm_num
  let x90 : ℝ := x87/(2 / 1)
  have hx90 : Bounds (171125990401 / 250000000000) (171128336901 / 250000000000) x90 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx89
  let x91 : ℝ := s⁻¹
  have hx91 : Bounds (2694177451459 / 250000000000) (10804112261209 / 1000000000000) x91 := by
    apply bounds_inv hs <;> norm_num
  let x92 : ℝ := x90*x91
  have hx92 : Bounds (7376700555151 / 1000000000000) (739555905181 / 100000000000) x92 := by
    apply bounds_mul hx90 hx91 <;> norm_num
  let x93 : ℝ := x90/s
  have hx93 : Bounds (7376700555151 / 1000000000000) (739555905181 / 100000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(93137 / 1000000)
  have hx95 : Bounds (1093137 / 1000000) (1093137 / 1000000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((93137 / 1000000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(93137 / 1000000)
  have hx96 : Bounds (1093137 / 1000000) (1093137 / 1000000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((93137 / 1000000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (11131443 / 125000000) (17810309 / 200000000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_4916.1) (by simpa only [div_one] using reflection_log_4916.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (97345537653 / 1000000000000) (97345538747 / 1000000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(93137 / 1000000)
  have hx99 : Bounds (-93137 / 1000000) (-93137 / 1000000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((93137 / 1000000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (906863 / 1000000) (906863 / 1000000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(93137 / 1000000)
  have hx101 : Bounds (906863 / 1000000) (906863 / 1000000) x101 := by
    exact hx100
  let x102 : ℝ := -(93137 / 1000000)
  have hx102 : Bounds (-93137 / 1000000) (-93137 / 1000000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((93137 / 1000000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (906863 / 1000000) (906863 / 1000000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(93137 / 1000000)
  have hx104 : Bounds (906863 / 1000000) (906863 / 1000000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-6110243 / 62500000) (-97763887 / 1000000000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_4917.1) (by simpa only [div_one] using reflection_log_4917.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-22164613191 / 250000000000) (-5541153241 / 62500000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (8687084889 / 1000000000000) (8687086891 / 1000000000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (1085885611 / 250000000000) (2171771723 / 500000000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (1085885611 / 250000000000) (2171771723 / 500000000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-2171771723 / 500000000000) (-1085885611 / 250000000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (344401818277 / 500000000000) (172200909639 / 250000000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (344401818277 / 500000000000) (172200909639 / 250000000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (93137 / 1000000)
  have hx114 : Bounds (344401818277 / 500000000000) (172200909639 / 250000000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(93373 / 1000000)
  have hx116 : Bounds (1093373 / 1000000) (1093373 / 1000000) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((93373 / 1000000) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(93373 / 1000000)
  have hx117 : Bounds (1093373 / 1000000) (1093373 / 1000000) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((93373 / 1000000) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (89267413 / 1000000000) (44633707 / 500000000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_4918.1) (by simpa only [div_one] using reflection_log_4918.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (48801289577 / 500000000000) (12200322531 / 125000000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(93373 / 1000000)
  have hx120 : Bounds (-93373 / 1000000) (-93373 / 1000000) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((93373 / 1000000) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (906627 / 1000000) (906627 / 1000000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(93373 / 1000000)
  have hx122 : Bounds (906627 / 1000000) (906627 / 1000000) x122 := by
    exact hx121
  let x123 : ℝ := -(93373 / 1000000)
  have hx123 : Bounds (-93373 / 1000000) (-93373 / 1000000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((93373 / 1000000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (906627 / 1000000) (906627 / 1000000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(93373 / 1000000)
  have hx125 : Bounds (906627 / 1000000) (906627 / 1000000) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-612651 / 6250000) (-98024159 / 1000000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_4919.1) (by simpa only [div_one] using reflection_log_4919.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-88871350109 / 1000000000000) (-88871349201 / 1000000000000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (1746245809 / 200000000000) (8731231047 / 1000000000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (2182807261 / 500000000000) (1091403881 / 250000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (2182807261 / 500000000000) (1091403881 / 250000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-1091403881 / 250000000000) (-2182807261 / 500000000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (172195391119 / 250000000000) (344390783239 / 500000000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (172195391119 / 250000000000) (344390783239 / 500000000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (93373 / 1000000)
  have hx135 : Bounds (172195391119 / 250000000000) (344390783239 / 500000000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(93137 / 1000000)
  have hx136 : Bounds (137408751921 / 200000000000) (688800183409 / 1000000000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((93137 / 1000000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(93373 / 1000000)
  have hx137 : Bounds (86098082617 / 125000000000) (138109107069 / 200000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((93373 / 1000000) : ℝ)) <;> norm_num
  have hc : Bounds (93137 / 1000000) (93373 / 1000000) c := by
    apply contact_bracket hc0 hc1 (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x93 by linarith [hx93.1])
      (show biasE c = x93*c by simpa +zetaDelta only [div_one] using heq)
    · have h1 : x93*(93137 / 1000000) ≤ (688800183409 / 1000000000000) := hx136.2
      have h2 : (344401818277 / 500000000000) ≤ biasE (93137 / 1000000) := hx114.1
      linarith
    · have h1 : biasE (93373 / 1000000) ≤ (344390783239 / 500000000000) := hx135.2
      have h2 : (86098082617 / 125000000000) ≤ x93*(93373 / 1000000) := hx137.1
      linarith
  let x138 : ℝ := Real.log (2 / 1)
  have hx138 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x138 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x139 : ℝ := (1 / 1)+(93373 / 1000000)
  have hx139 : Bounds (1093373 / 1000000) (1093373 / 1000000) x139 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((93373 / 1000000) : ℝ)) <;> norm_num
  let x140 : ℝ := (1 / 1)+(93373 / 1000000)
  have hx140 : Bounds (1093373 / 1000000) (1093373 / 1000000) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((93373 / 1000000) : ℝ)) <;> norm_num
  let x141 : ℝ := Real.log x140
  have hx141 : Bounds (89267413 / 1000000000) (44633707 / 500000000) x141 := by
    exact bounds_log hx140 (by norm_num) (by simpa only [div_one] using reflection_log_4918.1) (by simpa only [div_one] using reflection_log_4918.2)
  let x142 : ℝ := x139*x141
  have hx142 : Bounds (48801289577 / 500000000000) (12200322531 / 125000000000) x142 := by
    apply bounds_mul hx139 hx141 <;> norm_num
  let x143 : ℝ := -(93373 / 1000000)
  have hx143 : Bounds (-93373 / 1000000) (-93373 / 1000000) x143 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((93373 / 1000000) : ℝ))
  let x144 : ℝ := (1 / 1)+x143
  have hx144 : Bounds (906627 / 1000000) (906627 / 1000000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx143 <;> norm_num
  let x145 : ℝ := (1 / 1)-(93373 / 1000000)
  have hx145 : Bounds (906627 / 1000000) (906627 / 1000000) x145 := by
    exact hx144
  let x146 : ℝ := -(93373 / 1000000)
  have hx146 : Bounds (-93373 / 1000000) (-93373 / 1000000) x146 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((93373 / 1000000) : ℝ))
  let x147 : ℝ := (1 / 1)+x146
  have hx147 : Bounds (906627 / 1000000) (906627 / 1000000) x147 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx146 <;> norm_num
  let x148 : ℝ := (1 / 1)-(93373 / 1000000)
  have hx148 : Bounds (906627 / 1000000) (906627 / 1000000) x148 := by
    exact hx147
  let x149 : ℝ := Real.log x148
  have hx149 : Bounds (-612651 / 6250000) (-98024159 / 1000000000) x149 := by
    exact bounds_log hx148 (by norm_num) (by simpa only [div_one] using reflection_log_4919.1) (by simpa only [div_one] using reflection_log_4919.2)
  let x150 : ℝ := x145*x149
  have hx150 : Bounds (-88871350109 / 1000000000000) (-88871349201 / 1000000000000) x150 := by
    apply bounds_mul hx145 hx149 <;> norm_num
  let x151 : ℝ := x142+x150
  have hx151 : Bounds (1746245809 / 200000000000) (8731231047 / 1000000000000) x151 := by
    apply bounds_add hx142 hx150 <;> norm_num
  let x152 : ℝ := (2 / 1)⁻¹
  have hx152 : Bounds (1 / 2) (1 / 2) x152 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x153 : ℝ := x151*x152
  have hx153 : Bounds (2182807261 / 500000000000) (1091403881 / 250000000000) x153 := by
    apply bounds_mul hx151 hx152 <;> norm_num
  let x154 : ℝ := x151/(2 / 1)
  have hx154 : Bounds (2182807261 / 500000000000) (1091403881 / 250000000000) x154 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx153
  let x155 : ℝ := -x154
  have hx155 : Bounds (-1091403881 / 250000000000) (-2182807261 / 500000000000) x155 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx154
  let x156 : ℝ := x138+x155
  have hx156 : Bounds (172195391119 / 250000000000) (344390783239 / 500000000000) x156 := by
    apply bounds_add hx138 hx155 <;> norm_num
  let x157 : ℝ := x138-x154
  have hx157 : Bounds (172195391119 / 250000000000) (344390783239 / 500000000000) x157 := by
    exact hx156
  let x158 : ℝ := biasE (93373 / 1000000)
  have hx158 : Bounds (172195391119 / 250000000000) (344390783239 / 500000000000) x158 := by
    simpa +zetaDelta only [biasE, div_one] using hx157
  let x159 : ℝ := Real.log (2 / 1)
  have hx159 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x159 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x160 : ℝ := (1 / 1)+(93137 / 1000000)
  have hx160 : Bounds (1093137 / 1000000) (1093137 / 1000000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((93137 / 1000000) : ℝ)) <;> norm_num
  let x161 : ℝ := (1 / 1)+(93137 / 1000000)
  have hx161 : Bounds (1093137 / 1000000) (1093137 / 1000000) x161 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((93137 / 1000000) : ℝ)) <;> norm_num
  let x162 : ℝ := Real.log x161
  have hx162 : Bounds (11131443 / 125000000) (17810309 / 200000000) x162 := by
    exact bounds_log hx161 (by norm_num) (by simpa only [div_one] using reflection_log_4916.1) (by simpa only [div_one] using reflection_log_4916.2)
  let x163 : ℝ := x160*x162
  have hx163 : Bounds (97345537653 / 1000000000000) (97345538747 / 1000000000000) x163 := by
    apply bounds_mul hx160 hx162 <;> norm_num
  let x164 : ℝ := -(93137 / 1000000)
  have hx164 : Bounds (-93137 / 1000000) (-93137 / 1000000) x164 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((93137 / 1000000) : ℝ))
  let x165 : ℝ := (1 / 1)+x164
  have hx165 : Bounds (906863 / 1000000) (906863 / 1000000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx164 <;> norm_num
  let x166 : ℝ := (1 / 1)-(93137 / 1000000)
  have hx166 : Bounds (906863 / 1000000) (906863 / 1000000) x166 := by
    exact hx165
  let x167 : ℝ := -(93137 / 1000000)
  have hx167 : Bounds (-93137 / 1000000) (-93137 / 1000000) x167 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((93137 / 1000000) : ℝ))
  let x168 : ℝ := (1 / 1)+x167
  have hx168 : Bounds (906863 / 1000000) (906863 / 1000000) x168 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx167 <;> norm_num
  let x169 : ℝ := (1 / 1)-(93137 / 1000000)
  have hx169 : Bounds (906863 / 1000000) (906863 / 1000000) x169 := by
    exact hx168
  let x170 : ℝ := Real.log x169
  have hx170 : Bounds (-6110243 / 62500000) (-97763887 / 1000000000) x170 := by
    exact bounds_log hx169 (by norm_num) (by simpa only [div_one] using reflection_log_4917.1) (by simpa only [div_one] using reflection_log_4917.2)
  let x171 : ℝ := x166*x170
  have hx171 : Bounds (-22164613191 / 250000000000) (-5541153241 / 62500000000) x171 := by
    apply bounds_mul hx166 hx170 <;> norm_num
  let x172 : ℝ := x163+x171
  have hx172 : Bounds (8687084889 / 1000000000000) (8687086891 / 1000000000000) x172 := by
    apply bounds_add hx163 hx171 <;> norm_num
  let x173 : ℝ := (2 / 1)⁻¹
  have hx173 : Bounds (1 / 2) (1 / 2) x173 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x174 : ℝ := x172*x173
  have hx174 : Bounds (1085885611 / 250000000000) (2171771723 / 500000000000) x174 := by
    apply bounds_mul hx172 hx173 <;> norm_num
  let x175 : ℝ := x172/(2 / 1)
  have hx175 : Bounds (1085885611 / 250000000000) (2171771723 / 500000000000) x175 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx174
  let x176 : ℝ := -x175
  have hx176 : Bounds (-2171771723 / 500000000000) (-1085885611 / 250000000000) x176 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx175
  let x177 : ℝ := x159+x176
  have hx177 : Bounds (344401818277 / 500000000000) (172200909639 / 250000000000) x177 := by
    apply bounds_add hx159 hx176 <;> norm_num
  let x178 : ℝ := x159-x175
  have hx178 : Bounds (344401818277 / 500000000000) (172200909639 / 250000000000) x178 := by
    exact hx177
  let x179 : ℝ := biasE (93137 / 1000000)
  have hx179 : Bounds (344401818277 / 500000000000) (172200909639 / 250000000000) x179 := by
    simpa +zetaDelta only [biasE, div_one] using hx178
  let x180 : ℝ := biasE c
  have hx180 : Bounds (172195391119 / 250000000000) (172200909639 / 250000000000) x180 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx158.1 hx179.2
  let x181 : ℝ := Real.log (2 / 1)
  have hx181 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x181 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x182 : ℝ := c*c
  have hx182 : Bounds (8674500769 / 1000000000000) (8718517129 / 1000000000000) x182 := by
    apply bounds_mul hc hc <;> norm_num
  let x183 : ℝ := -x182
  have hx183 : Bounds (-8718517129 / 1000000000000) (-8674500769 / 1000000000000) x183 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx182
  let x184 : ℝ := (1 / 1)+x183
  have hx184 : Bounds (991281482871 / 1000000000000) (991325499231 / 1000000000000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx183 <;> norm_num
  let x185 : ℝ := (1 / 1)-x182
  have hx185 : Bounds (991281482871 / 1000000000000) (991325499231 / 1000000000000) x185 := by
    exact hx184
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (-4378373 / 500000000) (-8712343 / 1000000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_4920.1) (by simpa only [div_one] using reflection_log_4921.2)
  let x187 : ℝ := (2 / 1)⁻¹
  have hx187 : Bounds (1 / 2) (1 / 2) x187 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x188 : ℝ := x186*x187
  have hx188 : Bounds (-4378373 / 1000000000) (-8712343 / 2000000000) x188 := by
    apply bounds_mul hx186 hx187 <;> norm_num
  let x189 : ℝ := x186/(2 / 1)
  have hx189 : Bounds (-4378373 / 1000000000) (-8712343 / 2000000000) x189 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx188
  let x190 : ℝ := -x189
  have hx190 : Bounds (8712343 / 2000000000) (4378373 / 1000000000) x190 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx189
  let x191 : ℝ := x181+x190
  have hx191 : Bounds (1395006703 / 2000000000) (348762777 / 500000000) x191 := by
    apply bounds_add hx181 hx190 <;> norm_num
  let x192 : ℝ := x181-x189
  have hx192 : Bounds (1395006703 / 2000000000) (348762777 / 500000000) x192 := by
    exact hx191
  let x193 : ℝ := c*(1 / 1)
  have hx193 : Bounds (93137 / 1000000) (93373 / 1000000) x193 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x194 : ℝ := c*x193
  have hx194 : Bounds (8674500769 / 1000000000000) (8718517129 / 1000000000000) x194 := by
    apply bounds_mul hc hx193 <;> norm_num
  let x195 : ℝ := c^2
  have hx195 : Bounds (8674500769 / 1000000000000) (8718517129 / 1000000000000) x195 := by
    (convert hx194 using 1; ring)
  let x196 : ℝ := -x195
  have hx196 : Bounds (-8718517129 / 1000000000000) (-8674500769 / 1000000000000) x196 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx195
  let x197 : ℝ := (1 / 1)+x196
  have hx197 : Bounds (991281482871 / 1000000000000) (991325499231 / 1000000000000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx196 <;> norm_num
  let x198 : ℝ := (1 / 1)-x195
  have hx198 : Bounds (991281482871 / 1000000000000) (991325499231 / 1000000000000) x198 := by
    exact hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (1093137 / 1000000) (1093373 / 1000000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-93373 / 1000000) (-93137 / 1000000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (906627 / 1000000) (906863 / 1000000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (906627 / 1000000) (906863 / 1000000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (1102702392753 / 1000000000000) (1102989432259 / 1000000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (602702392753 / 500000000000) (602989432259 / 500000000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (602702392753 / 500000000000) (602989432259 / 500000000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (23351929 / 125000000) (187291573 / 1000000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_4922.1) (by simpa only [div_one] using reflection_log_4923.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (23351929 / 250000000) (187291573 / 2000000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (23351929 / 250000000) (187291573 / 2000000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (1 / 1)+a
  have hx210 : Bounds (11853 / 10000) (5927 / 5000) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) ha <;> norm_num
  let x211 : ℝ := -a
  have hx211 : Bounds (-927 / 5000) (-1853 / 10000) x211 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg ha
  let x212 : ℝ := (1 / 1)+x211
  have hx212 : Bounds (4073 / 5000) (8147 / 10000) x212 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx211 <;> norm_num
  let x213 : ℝ := (1 / 1)-a
  have hx213 : Bounds (4073 / 5000) (8147 / 10000) x213 := by
    exact hx212
  let x214 : ℝ := x213⁻¹
  have hx214 : Bounds (153430710691 / 125000000000) (245519273263 / 200000000000) x214 := by
    apply bounds_inv hx213 <;> norm_num
  let x215 : ℝ := x210*x214
  have hx215 : Bounds (90930710691 / 62500000000) (145519273263 / 100000000000) x215 := by
    apply bounds_mul hx210 hx214 <;> norm_num
  let x216 : ℝ := x210/x213
  have hx216 : Bounds (90930710691 / 62500000000) (145519273263 / 100000000000) x216 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx215
  let x217 : ℝ := Real.log x216
  have hx217 : Bounds (187465619 / 500000000) (75027671 / 200000000) x217 := by
    exact bounds_log hx216 (by norm_num) (by simpa only [div_one] using reflection_log_4924.1) (by simpa only [div_one] using reflection_log_4925.2)
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (187465619 / 1000000000) (75027671 / 400000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (187465619 / 1000000000) (75027671 / 400000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := (2 / 1)*x192
  have hx221 : Bounds (1395006703 / 1000000000) (348762777 / 250000000) x221 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x222 : ℝ := c*(1 / 1)
  have hx222 : Bounds (93137 / 1000000) (93373 / 1000000) x222 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x223 : ℝ := c*x222
  have hx223 : Bounds (8674500769 / 1000000000000) (8718517129 / 1000000000000) x223 := by
    apply bounds_mul hc hx222 <;> norm_num
  let x224 : ℝ := c^2
  have hx224 : Bounds (8674500769 / 1000000000000) (8718517129 / 1000000000000) x224 := by
    (convert hx223 using 1; ring)
  let x225 : ℝ := -x224
  have hx225 : Bounds (-8718517129 / 1000000000000) (-8674500769 / 1000000000000) x225 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx224
  let x226 : ℝ := x221+x225
  have hx226 : Bounds (1386288185871 / 1000000000000) (1386376607231 / 1000000000000) x226 := by
    apply bounds_add hx221 hx225 <;> norm_num
  let x227 : ℝ := x221-x224
  have hx227 : Bounds (1386288185871 / 1000000000000) (1386376607231 / 1000000000000) x227 := by
    exact hx226
  let x228 : ℝ := x180*x227
  have hx228 : Bounds (477424872739 / 500000000000) (95494125147 / 100000000000) x228 := by
    apply bounds_mul hx180 hx227 <;> norm_num
  let x229 : ℝ := (2 / 1)*x90
  have hx229 : Bounds (171125990401 / 125000000000) (171128336901 / 125000000000) x229 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x230 : ℝ := x198*(1 / 1)
  have hx230 : Bounds (991281482871 / 1000000000000) (991325499231 / 1000000000000) x230 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x231 : ℝ := x198*x230
  have hx231 : Bounds (491319489141 / 500000000000) (491363122713 / 500000000000) x231 := by
    apply bounds_mul hx198 hx230 <;> norm_num
  let x232 : ℝ := x198^2
  have hx232 : Bounds (491319489141 / 500000000000) (491363122713 / 500000000000) x232 := by
    (convert hx231 using 1; ring)
  let x233 : ℝ := x229*x232
  have hx233 : Bounds (1345240546921 / 1000000000000) (134537846407 / 100000000000) x233 := by
    apply bounds_mul hx229 hx232 <;> norm_num
  let x234 : ℝ := x192*(1 / 1)
  have hx234 : Bounds (1395006703 / 2000000000) (348762777 / 500000000) x234 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x235 : ℝ := x192*x234
  have hx235 : Bounds (486510925353 / 1000000000000) (121635474621 / 250000000000) x235 := by
    apply bounds_mul hx192 hx234 <;> norm_num
  let x236 : ℝ := x192*x235
  have hx236 : Bounds (13573720039 / 40000000000) (67875081457 / 200000000000) x236 := by
    apply bounds_mul hx192 hx235 <;> norm_num
  let x237 : ℝ := x192^3
  have hx237 : Bounds (13573720039 / 40000000000) (67875081457 / 200000000000) x237 := by
    (convert hx236 using 1; ring)
  let x238 : ℝ := x233*x237
  have hx238 : Bounds (18259918569 / 40000000000) (456588364197 / 1000000000000) x238 := by
    apply bounds_mul hx233 hx237 <;> norm_num
  let x239 : ℝ := x238⁻¹
  have hx239 : Bounds (438031311533 / 200000000000) (438118054567 / 200000000000) x239 := by
    apply bounds_inv hx238 <;> norm_num
  let x240 : ℝ := x228*x239
  have hx240 : Bounds (2091270431643 / 1000000000000) (10459425083 / 5000000000) x240 := by
    apply bounds_mul hx228 hx239 <;> norm_num
  let x241 : ℝ := x228/x238
  have hx241 : Bounds (2091270431643 / 1000000000000) (10459425083 / 5000000000) x241 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx240
  let x242 : ℝ := -x209
  have hx242 : Bounds (-187291573 / 2000000000) (-23351929 / 250000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x243 : ℝ := (2 / 1)*x192
  have hx243 : Bounds (1395006703 / 1000000000) (348762777 / 250000000) x243 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x244 : ℝ := c*(1 / 1)
  have hx244 : Bounds (93137 / 1000000) (93373 / 1000000) x244 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x245 : ℝ := c*x244
  have hx245 : Bounds (8674500769 / 1000000000000) (8718517129 / 1000000000000) x245 := by
    apply bounds_mul hc hx244 <;> norm_num
  let x246 : ℝ := c^2
  have hx246 : Bounds (8674500769 / 1000000000000) (8718517129 / 1000000000000) x246 := by
    (convert hx245 using 1; ring)
  let x247 : ℝ := -x246
  have hx247 : Bounds (-8718517129 / 1000000000000) (-8674500769 / 1000000000000) x247 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx246
  let x248 : ℝ := x243+x247
  have hx248 : Bounds (1386288185871 / 1000000000000) (1386376607231 / 1000000000000) x248 := by
    apply bounds_add hx243 hx247 <;> norm_num
  let x249 : ℝ := x243-x246
  have hx249 : Bounds (1386288185871 / 1000000000000) (1386376607231 / 1000000000000) x249 := by
    exact hx248
  let x250 : ℝ := x242*x249
  have hx250 : Bounds (-12982832777 / 100000000000) (-129490013159 / 1000000000000) x250 := by
    apply bounds_mul hx242 hx249 <;> norm_num
  let x251 : ℝ := x198⁻¹
  have hx251 : Bounds (504375203087 / 500000000000) (126099399777 / 125000000000) x251 := by
    apply bounds_inv hx198 <;> norm_num
  let x252 : ℝ := c*x251
  have hx252 : Bounds (93951986579 / 1000000000000) (23548558511 / 250000000000) x252 := by
    apply bounds_mul hc hx251 <;> norm_num
  let x253 : ℝ := c/x198
  have hx253 : Bounds (93951986579 / 1000000000000) (23548558511 / 250000000000) x253 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx252
  let x254 : ℝ := (2 / 1)*x253
  have hx254 : Bounds (93951986579 / 500000000000) (23548558511 / 125000000000) x254 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx253 <;> norm_num
  let x255 : ℝ := (2 / 1)*c
  have hx255 : Bounds (93137 / 500000) (93373 / 500000) x255 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hc <;> norm_num
  let x256 : ℝ := -x255
  have hx256 : Bounds (-93373 / 500000) (-93137 / 500000) x256 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx255
  let x257 : ℝ := x254+x256
  have hx257 : Bounds (578986579 / 500000000000) (264308511 / 125000000000) x257 := by
    apply bounds_add hx254 hx256 <;> norm_num
  let x258 : ℝ := x254-x255
  have hx258 : Bounds (578986579 / 500000000000) (264308511 / 125000000000) x258 := by
    exact hx257
  let x259 : ℝ := x180*x258
  have hx259 : Bounds (797590563 / 1000000000000) (1456453313 / 1000000000000) x259 := by
    apply bounds_mul hx180 hx258 <;> norm_num
  let x260 : ℝ := x250+x259
  have hx260 : Bounds (-129030737207 / 1000000000000) (-64016779923 / 500000000000) x260 := by
    apply bounds_add hx250 hx259 <;> norm_num
  let x261 : ℝ := (2 / 1)*x90
  have hx261 : Bounds (171125990401 / 125000000000) (171128336901 / 125000000000) x261 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x262 : ℝ := x198*(1 / 1)
  have hx262 : Bounds (991281482871 / 1000000000000) (991325499231 / 1000000000000) x262 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x263 : ℝ := x198*x262
  have hx263 : Bounds (491319489141 / 500000000000) (491363122713 / 500000000000) x263 := by
    apply bounds_mul hx198 hx262 <;> norm_num
  let x264 : ℝ := x198^2
  have hx264 : Bounds (491319489141 / 500000000000) (491363122713 / 500000000000) x264 := by
    (convert hx263 using 1; ring)
  let x265 : ℝ := x261*x264
  have hx265 : Bounds (1345240546921 / 1000000000000) (134537846407 / 100000000000) x265 := by
    apply bounds_mul hx261 hx264 <;> norm_num
  let x266 : ℝ := x192*(1 / 1)
  have hx266 : Bounds (1395006703 / 2000000000) (348762777 / 500000000) x266 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x267 : ℝ := x192*x266
  have hx267 : Bounds (486510925353 / 1000000000000) (121635474621 / 250000000000) x267 := by
    apply bounds_mul hx192 hx266 <;> norm_num
  let x268 : ℝ := x192*x267
  have hx268 : Bounds (13573720039 / 40000000000) (67875081457 / 200000000000) x268 := by
    apply bounds_mul hx192 hx267 <;> norm_num
  let x269 : ℝ := x192^3
  have hx269 : Bounds (13573720039 / 40000000000) (67875081457 / 200000000000) x269 := by
    (convert hx268 using 1; ring)
  let x270 : ℝ := x265*x269
  have hx270 : Bounds (18259918569 / 40000000000) (456588364197 / 1000000000000) x270 := by
    apply bounds_mul hx265 hx269 <;> norm_num
  let x271 : ℝ := x270⁻¹
  have hx271 : Bounds (438031311533 / 200000000000) (438118054567 / 200000000000) x271 := by
    apply bounds_inv hx270 <;> norm_num
  let x272 : ℝ := x260*x271
  have hx272 : Bounds (-282653477823 / 1000000000000) (-280413540697 / 1000000000000) x272 := by
    apply bounds_mul hx260 hx271 <;> norm_num
  let x273 : ℝ := x260/x270
  have hx273 : Bounds (-282653477823 / 1000000000000) (-280413540697 / 1000000000000) x273 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx272
  let x274 : ℝ := (4 / 1)*c
  have hx274 : Bounds (93137 / 250000) (93373 / 250000) x274 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hc <;> norm_num
  let x275 : ℝ := x198⁻¹
  have hx275 : Bounds (504375203087 / 500000000000) (126099399777 / 125000000000) x275 := by
    apply bounds_inv hx198 <;> norm_num
  let x276 : ℝ := x274*x275
  have hx276 : Bounds (375807946319 / 1000000000000) (376776936173 / 1000000000000) x276 := by
    apply bounds_mul hx274 hx275 <;> norm_num
  let x277 : ℝ := x274/x198
  have hx277 : Bounds (375807946319 / 1000000000000) (376776936173 / 1000000000000) x277 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx276
  let x278 : ℝ := (3 / 1)*c
  have hx278 : Bounds (279411 / 1000000) (280119 / 1000000) x278 := by
    apply bounds_mul (bounds_const ((3 / 1) : ℝ)) hc <;> norm_num
  let x279 : ℝ := x198*x192
  have hx279 : Bounds (345711078291 / 500000000000) (345737434023 / 500000000000) x279 := by
    apply bounds_mul hx198 hx192 <;> norm_num
  let x280 : ℝ := x279⁻¹
  have hx280 : Bounds (289236831651 / 200000000000) (1446294409979 / 1000000000000) x280 := by
    apply bounds_inv hx279 <;> norm_num
  let x281 : ℝ := x278*x280
  have hx281 : Bounds (202039880921 / 500000000000) (405134543829 / 1000000000000) x281 := by
    apply bounds_mul hx278 hx280 <;> norm_num
  let x282 : ℝ := x278/x279
  have hx282 : Bounds (202039880921 / 500000000000) (405134543829 / 1000000000000) x282 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx281
  let x283 : ℝ := -x282
  have hx283 : Bounds (-405134543829 / 1000000000000) (-202039880921 / 500000000000) x283 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx282
  let x284 : ℝ := x277+x283
  have hx284 : Bounds (-2932659751 / 100000000000) (-27302825669 / 1000000000000) x284 := by
    apply bounds_add hx277 hx283 <;> norm_num
  let x285 : ℝ := x277-x282
  have hx285 : Bounds (-2932659751 / 100000000000) (-27302825669 / 1000000000000) x285 := by
    exact hx284
  let x286 : ℝ := x241*x285
  have hx286 : Bounds (-383424187 / 6250000000) (-57097592021 / 1000000000000) x286 := by
    apply bounds_mul hx241 hx285 <;> norm_num
  let x287 : ℝ := x273+x286
  have hx287 : Bounds (-344001347743 / 1000000000000) (-168755566359 / 500000000000) x287 := by
    apply bounds_add hx273 hx286 <;> norm_num
  let x288 : ℝ := (2 / 1)*x192
  have hx288 : Bounds (1395006703 / 1000000000) (348762777 / 250000000) x288 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x289 : ℝ := c*(1 / 1)
  have hx289 : Bounds (93137 / 1000000) (93373 / 1000000) x289 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x290 : ℝ := c*x289
  have hx290 : Bounds (8674500769 / 1000000000000) (8718517129 / 1000000000000) x290 := by
    apply bounds_mul hc hx289 <;> norm_num
  let x291 : ℝ := c^2
  have hx291 : Bounds (8674500769 / 1000000000000) (8718517129 / 1000000000000) x291 := by
    (convert hx290 using 1; ring)
  let x292 : ℝ := -x291
  have hx292 : Bounds (-8718517129 / 1000000000000) (-8674500769 / 1000000000000) x292 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx291
  let x293 : ℝ := x288+x292
  have hx293 : Bounds (1386288185871 / 1000000000000) (1386376607231 / 1000000000000) x293 := by
    apply bounds_add hx288 hx292 <;> norm_num
  let x294 : ℝ := x288-x291
  have hx294 : Bounds (1386288185871 / 1000000000000) (1386376607231 / 1000000000000) x294 := by
    exact hx293
  let x295 : ℝ := c*x294
  have hx295 : Bounds (129114722767 / 1000000000000) (129450142947 / 1000000000000) x295 := by
    apply bounds_mul hc hx294 <;> norm_num
  let x296 : ℝ := x198*(1 / 1)
  have hx296 : Bounds (991281482871 / 1000000000000) (991325499231 / 1000000000000) x296 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x297 : ℝ := x198*x296
  have hx297 : Bounds (491319489141 / 500000000000) (491363122713 / 500000000000) x297 := by
    apply bounds_mul hx198 hx296 <;> norm_num
  let x298 : ℝ := x198^2
  have hx298 : Bounds (491319489141 / 500000000000) (491363122713 / 500000000000) x298 := by
    (convert hx297 using 1; ring)
  let x299 : ℝ := x192*(1 / 1)
  have hx299 : Bounds (1395006703 / 2000000000) (348762777 / 500000000) x299 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x300 : ℝ := x192*x299
  have hx300 : Bounds (486510925353 / 1000000000000) (121635474621 / 250000000000) x300 := by
    apply bounds_mul hx192 hx299 <;> norm_num
  let x301 : ℝ := x192^2
  have hx301 : Bounds (486510925353 / 1000000000000) (121635474621 / 250000000000) x301 := by
    (convert hx300 using 1; ring)
  let x302 : ℝ := x298*x301
  have hx302 : Bounds (478064598611 / 1000000000000) (23906874657 / 50000000000) x302 := by
    apply bounds_mul hx298 hx301 <;> norm_num
  let x303 : ℝ := x302⁻¹
  have hx303 : Bounds (1045724309793 / 500000000000) (2091767520343 / 1000000000000) x303 := by
    apply bounds_inv hx302 <;> norm_num
  let x304 : ℝ := x295*x303
  have hx304 : Bounds (270036808699 / 1000000000000) (270779604521 / 1000000000000) x304 := by
    apply bounds_mul hx295 hx303 <;> norm_num
  let x305 : ℝ := x295/x302
  have hx305 : Bounds (270036808699 / 1000000000000) (270779604521 / 1000000000000) x305 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx304
  let x306 : ℝ := c*x220
  have hx306 : Bounds (4364996339 / 250000000000) (17513896811 / 1000000000000) x306 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x307 : ℝ := x180+x306
  have hx307 : Bounds (88280193729 / 125000000000) (706317535367 / 1000000000000) x307 := by
    apply bounds_add hx180 hx306 <;> norm_num
  let x308 : ℝ := x307*(1 / 1)
  have hx308 : Bounds (88280193729 / 125000000000) (706317535367 / 1000000000000) x308 := by
    apply bounds_mul hx307 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x309 : ℝ := x307*x308
  have hx309 : Bounds (498777126709 / 1000000000000) (498884460767 / 1000000000000) x309 := by
    apply bounds_mul hx307 hx308 <;> norm_num
  let x310 : ℝ := x307^2
  have hx310 : Bounds (498777126709 / 1000000000000) (498884460767 / 1000000000000) x310 := by
    (convert hx309 using 1; ring)
  let x311 : ℝ := x287*x310
  have hx311 : Bounds (-21452115859 / 125000000000) (-168342833009 / 1000000000000) x311 := by
    apply bounds_mul hx287 hx310 <;> norm_num
  let x312 : ℝ := (2 / 1)*x241
  have hx312 : Bounds (2091270431643 / 500000000000) (10459425083 / 2500000000) x312 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx241 <;> norm_num
  let x313 : ℝ := c*x220
  have hx313 : Bounds (4364996339 / 250000000000) (17513896811 / 1000000000000) x313 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x314 : ℝ := x180+x313
  have hx314 : Bounds (88280193729 / 125000000000) (706317535367 / 1000000000000) x314 := by
    apply bounds_add hx180 hx313 <;> norm_num
  let x315 : ℝ := x312*x314
  have hx315 : Bounds (1476942070761 / 500000000000) (2955070138393 / 1000000000000) x315 := by
    apply bounds_mul hx312 hx314 <;> norm_num
  let x316 : ℝ := -x209
  have hx316 : Bounds (-187291573 / 2000000000) (-23351929 / 250000000) x316 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x317 : ℝ := x220+x316
  have hx317 : Bounds (37527933 / 400000000) (188322923 / 2000000000) x317 := by
    apply bounds_add hx220 hx316 <;> norm_num
  let x318 : ℝ := x220-x209
  have hx318 : Bounds (37527933 / 400000000) (188322923 / 2000000000) x318 := by
    exact hx317
  let x319 : ℝ := x315*x318
  have hx319 : Bounds (138566457691 / 500000000000) (278253723067 / 1000000000000) x319 := by
    apply bounds_mul hx315 hx318 <;> norm_num
  let x320 : ℝ := x311+x319
  have hx320 : Bounds (10551598851 / 100000000000) (54955445029 / 500000000000) x320 := by
    apply bounds_add hx311 hx319 <;> norm_num
  let x321 : ℝ := a*(1 / 1)
  have hx321 : Bounds (1853 / 10000) (927 / 5000) x321 := by
    apply bounds_mul ha (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x322 : ℝ := a*x321
  have hx322 : Bounds (3433609 / 100000000) (859329 / 25000000) x322 := by
    apply bounds_mul ha hx321 <;> norm_num
  let x323 : ℝ := a^2
  have hx323 : Bounds (3433609 / 100000000) (859329 / 25000000) x323 := by
    (convert hx322 using 1; ring)
  let x324 : ℝ := -x323
  have hx324 : Bounds (-859329 / 25000000) (-3433609 / 100000000) x324 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx323
  let x325 : ℝ := (1 / 1)+x324
  have hx325 : Bounds (24140671 / 25000000) (96566391 / 100000000) x325 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx324 <;> norm_num
  let x326 : ℝ := (1 / 1)-x323
  have hx326 : Bounds (24140671 / 25000000) (96566391 / 100000000) x326 := by
    exact hx325
  let x327 : ℝ := x326⁻¹
  have hx327 : Bounds (517778488791 / 500000000000) (1035596732171 / 1000000000000) x327 := by
    apply bounds_inv hx326 <;> norm_num
  let x328 : ℝ := (1 / 1)*x327
  have hx328 : Bounds (517778488791 / 500000000000) (1035596732171 / 1000000000000) x328 := by
    apply bounds_mul (bounds_const ((1 / 1) : ℝ)) hx327 <;> norm_num
  let x329 : ℝ := (1 / 1)/x326
  have hx329 : Bounds (517778488791 / 500000000000) (1035596732171 / 1000000000000) x329 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx328
  let x330 : ℝ := x329*x305
  have hx330 : Bounds (69909625363 / 250000000000) (280418473581 / 1000000000000) x330 := by
    apply bounds_mul hx329 hx305 <;> norm_num
  let x331 : ℝ := x320+x330
  have hx331 : Bounds (192577244981 / 500000000000) (390329363639 / 1000000000000) x331 := by
    apply bounds_add hx320 hx330 <;> norm_num
  let x332 : ℝ := x180*(1 / 1)
  have hx332 : Bounds (172195391119 / 250000000000) (172200909639 / 250000000000) x332 := by
    apply bounds_mul hx180 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x333 : ℝ := x180*x332
  have hx333 : Bounds (237210021781 / 500000000000) (59306306561 / 125000000000) x333 := by
    apply bounds_mul hx180 hx332 <;> norm_num
  let x334 : ℝ := x180^2
  have hx334 : Bounds (237210021781 / 500000000000) (59306306561 / 125000000000) x334 := by
    (convert hx333 using 1; ring)
  let x335 : ℝ := x331*x334
  have hx335 : Bounds (36545001981 / 200000000000) (92595971599 / 500000000000) x335 := by
    apply bounds_mul hx331 hx334 <;> norm_num
  let x336 : ℝ := x90*x192
  have hx336 : Bounds (477443807333 / 1000000000000) (59683194001 / 125000000000) x336 := by
    apply bounds_mul hx90 hx192 <;> norm_num
  let x337 : ℝ := x336⁻¹
  have hx337 : Bounds (2094391932139 / 1000000000000) (2094487319013 / 1000000000000) x337 := by
    apply bounds_inv hx336 <;> norm_num
  let x338 : ℝ := x335*x337
  have hx338 : Bounds (76539557309 / 200000000000) (96970544153 / 250000000000) x338 := by
    apply bounds_mul hx335 hx337 <;> norm_num
  let x339 : ℝ := x335/x336
  have hx339 : Bounds (76539557309 / 200000000000) (96970544153 / 250000000000) x339 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx338
  have hu : x339 < (1830756905691727590892290793 / 4662533935382440500000000000) := lt_of_le_of_lt hx339.2 (by norm_num)
  simpa +zetaDelta only [ScFormula,Kprime,K,Mprime,SmallMean.A,biasB,div_one,pow_two] using hu

open GeneralCK.Reflection
/-- Uniform derivative enclosure including input boxes with z=0. -/
theorem derivative_bound_353 {a z s : ℝ}
    (ha : a ∈ Set.Icc ((1853 / 10000):ℝ) ((927 / 5000)))
    (hz : z ∈ Set.Icc (0:ℝ) (1/1000))
    (hs : s ∈ Set.Ioo (a*(1-z)/2) (a*(1+z)/2)) :
    P a ((biasE a+biasE (a*z))/2) s ≤ (1830756905691727590892290793 / 4662533935382440500000000000) := by
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
  have hsl : (1851147 / 20000000) ≤ s := by
    have h := mul_le_mul ha.1 (show (999/1000:ℝ) ≤ 1-z by linarith [hz.2])
      (by norm_num : (0:ℝ) ≤ 999/1000) ha0.le
    nlinarith [hs.1]
  have hsu : s ≤ (927927 / 10000000) := by
    have h := mul_le_mul ha.2 (show 1+z ≤ (1001/1000:ℝ) by linarith [hz.2])
      (by linarith [hz.1] : 0 ≤ 1+z) (by norm_num : (0:ℝ) ≤ (927 / 5000))
    nlinarith [hs.2]
  have hy := div_pos he hs0
  have hc := biasContact_mem hy
  have heq : biasE (biasContact (((biasE a+biasE (a*z))/2)/s)) =
      (((biasE a+biasE (a*z))/2)/s)*biasContact (((biasE a+biasE (a*z))/2)/s) := by
    exact (div_eq_iff hc.1.ne').mp (biasR_biasContact hy)
  have hb := derivative_leaf_353 a z s _ ha hz ⟨hsl,hsu⟩ hc.1.le hc.2.le heq
  rw [P_eq_formula ha0 ha1 he hs0]
  exact hb.le

/-- Checked low-ratio strip: includes arbitrarily small positive z. -/
theorem curvature_leaf_353 {a z : ℝ}
    (ha : a ∈ Set.Icc ((1853 / 10000):ℝ) ((927 / 5000)))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < curvature a (a*z) := by
  have ha0 : 0 < a := by linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  apply curvature_pos_of_derivative_bound ha0 ha1 hz.1 (by linarith [hz.2])
    (fun s hs => derivative_bound_353 ha ⟨hz.1.le,hz.2⟩ hs) (M := (1830756905691727590892290793 / 4662533935382440500000000000))
  exact lt_of_lt_of_le (by norm_num : (1830756905691727590892290793 / 4662533935382440500000000000) < 2*((1853 / 10000):ℝ)/(1-((1853 / 10000):ℝ)^2)^2)
    (base_mono (by norm_num) ha.1 ha1)

end GeneralCK.Certificates.LowRatioFamily

end


