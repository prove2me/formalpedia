-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0895__6
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Cell0895__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T07:33:13.188837+00:00
-- url     : https://prove2.me/theorems/b0d5cfda-b0d1-4b3a-8bd5-db95fd0b28bd
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Cell0895 (+5 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Cell0896, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Cell0895 (+5 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Cell0896, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0897, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0898, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0899, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0900)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Cell0895 (+5 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Cell0896, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0897, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0898, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0899, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0900)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Cell0895 (+5 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Cell0896, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0897, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0898, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0899, GeneralCK.Certificates.Generated.LowRatioFamily.Cell0900) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Cell0895 (+5 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Cell0896, GeneralCK/Certificates/Generated/LowRatioFamily/Cell0897, GeneralCK/Certificates/Generated/LowRatioFamily/Cell0898, GeneralCK/Certificates/Generated/LowRatioFamily/Cell0899, GeneralCK/Certificates/Generated/LowRatioFamily/Cell0900).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0000__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0193__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0106__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0196__3

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Cell0895 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
theorem derivative_leaf_895 (a z s c : ℝ)
    (ha : Bounds (99 / 200) (62 / 125) a) (hz : Bounds 0 (1/1000) z)
    (hs : Bounds (98901 / 400000) (31031 / 125000) s) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (heq : biasE c = (((biasE a+biasE (a*z))/2)/s)*c) :
    ScFormula c a ((biasE a+biasE (a*z))/2)*(biasE c)^2 /
      (((biasE a+biasE (a*z))/2)*biasB c) < (355477719285426127731 / 227994900250000000000) := by
  let x0 : ℝ := Real.log (2 / 1)
  have hx0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x0 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x1 : ℝ := (1 / 1)+(62 / 125)
  have hx1 : Bounds (187 / 125) (187 / 125) x1 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((62 / 125) : ℝ)) <;> norm_num
  let x2 : ℝ := (1 / 1)+(62 / 125)
  have hx2 : Bounds (187 / 125) (187 / 125) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((62 / 125) : ℝ)) <;> norm_num
  let x3 : ℝ := Real.log x2
  have hx3 : Bounds (402794879 / 1000000000) (629367 / 1562500) x3 := by
    exact bounds_log hx2 (by norm_num) (by simpa only [div_one] using reflection_log_12484.1) (by simpa only [div_one] using reflection_log_12484.2)
  let x4 : ℝ := x1*x3
  have hx4 : Bounds (75322642373 / 125000000000) (117691629 / 195312500) x4 := by
    apply bounds_mul hx1 hx3 <;> norm_num
  let x5 : ℝ := -(62 / 125)
  have hx5 : Bounds (-62 / 125) (-62 / 125) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((62 / 125) : ℝ))
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (63 / 125) (63 / 125) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-(62 / 125)
  have hx7 : Bounds (63 / 125) (63 / 125) x7 := by
    exact hx6
  let x8 : ℝ := -(62 / 125)
  have hx8 : Bounds (-62 / 125) (-62 / 125) x8 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((62 / 125) : ℝ))
  let x9 : ℝ := (1 / 1)+x8
  have hx9 : Bounds (63 / 125) (63 / 125) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx8 <;> norm_num
  let x10 : ℝ := (1 / 1)-(62 / 125)
  have hx10 : Bounds (63 / 125) (63 / 125) x10 := by
    exact hx9
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (-685179011 / 1000000000) (-68517901 / 100000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_12485.1) (by simpa only [div_one] using reflection_log_12485.2)
  let x12 : ℝ := x7*x11
  have hx12 : Bounds (-43166277693 / 125000000000) (-4316627763 / 12500000000) x12 := by
    apply bounds_mul hx7 hx11 <;> norm_num
  let x13 : ℝ := x4+x12
  have hx13 : Bounds (803909117 / 3125000000) (3215636493 / 12500000000) x13 := by
    apply bounds_add hx4 hx12 <;> norm_num
  let x14 : ℝ := (2 / 1)⁻¹
  have hx14 : Bounds (1 / 2) (1 / 2) x14 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x15 : ℝ := x13*x14
  have hx15 : Bounds (803909117 / 6250000000) (3215636493 / 25000000000) x15 := by
    apply bounds_mul hx13 hx14 <;> norm_num
  let x16 : ℝ := x13/(2 / 1)
  have hx16 : Bounds (803909117 / 6250000000) (3215636493 / 25000000000) x16 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx15
  let x17 : ℝ := -x16
  have hx17 : Bounds (-3215636493 / 25000000000) (-803909117 / 6250000000) x17 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx16
  let x18 : ℝ := x0+x17
  have hx18 : Bounds (14113043007 / 25000000000) (14113043057 / 25000000000) x18 := by
    apply bounds_add hx0 hx17 <;> norm_num
  let x19 : ℝ := x0-x16
  have hx19 : Bounds (14113043007 / 25000000000) (14113043057 / 25000000000) x19 := by
    exact hx18
  let x20 : ℝ := biasE (62 / 125)
  have hx20 : Bounds (14113043007 / 25000000000) (14113043057 / 25000000000) x20 := by
    simpa +zetaDelta only [biasE, div_one] using hx19
  let x21 : ℝ := Real.log (2 / 1)
  have hx21 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x21 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x22 : ℝ := (1 / 1)+(99 / 200)
  have hx22 : Bounds (299 / 200) (299 / 200) x22 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((99 / 200) : ℝ)) <;> norm_num
  let x23 : ℝ := (1 / 1)+(99 / 200)
  have hx23 : Bounds (299 / 200) (299 / 200) x23 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((99 / 200) : ℝ)) <;> norm_num
  let x24 : ℝ := Real.log x23
  have hx24 : Bounds (201063103 / 500000000) (402126207 / 1000000000) x24 := by
    exact bounds_log hx23 (by norm_num) (by simpa only [div_one] using reflection_log_12470.1) (by simpa only [div_one] using reflection_log_12470.2)
  let x25 : ℝ := x22*x24
  have hx25 : Bounds (60117867797 / 100000000000) (120235735893 / 200000000000) x25 := by
    apply bounds_mul hx22 hx24 <;> norm_num
  let x26 : ℝ := -(99 / 200)
  have hx26 : Bounds (-99 / 200) (-99 / 200) x26 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((99 / 200) : ℝ))
  let x27 : ℝ := (1 / 1)+x26
  have hx27 : Bounds (101 / 200) (101 / 200) x27 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx26 <;> norm_num
  let x28 : ℝ := (1 / 1)-(99 / 200)
  have hx28 : Bounds (101 / 200) (101 / 200) x28 := by
    exact hx27
  let x29 : ℝ := -(99 / 200)
  have hx29 : Bounds (-99 / 200) (-99 / 200) x29 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((99 / 200) : ℝ))
  let x30 : ℝ := (1 / 1)+x29
  have hx30 : Bounds (101 / 200) (101 / 200) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx29 <;> norm_num
  let x31 : ℝ := (1 / 1)-(99 / 200)
  have hx31 : Bounds (101 / 200) (101 / 200) x31 := by
    exact hx30
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (-13663937 / 20000000) (-683196849 / 1000000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_12471.1) (by simpa only [div_one] using reflection_log_12471.2)
  let x33 : ℝ := x28*x32
  have hx33 : Bounds (-1380057637 / 4000000000) (-69002881749 / 200000000000) x33 := by
    apply bounds_mul hx28 hx32 <;> norm_num
  let x34 : ℝ := x25+x33
  have hx34 : Bounds (3202053359 / 12500000000) (400256673 / 1562500000) x34 := by
    apply bounds_add hx25 hx33 <;> norm_num
  let x35 : ℝ := (2 / 1)⁻¹
  have hx35 : Bounds (1 / 2) (1 / 2) x35 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x36 : ℝ := x34*x35
  have hx36 : Bounds (3202053359 / 25000000000) (400256673 / 3125000000) x36 := by
    apply bounds_mul hx34 hx35 <;> norm_num
  let x37 : ℝ := x34/(2 / 1)
  have hx37 : Bounds (3202053359 / 25000000000) (400256673 / 3125000000) x37 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx36
  let x38 : ℝ := -x37
  have hx38 : Bounds (-400256673 / 3125000000) (-3202053359 / 25000000000) x38 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx37
  let x39 : ℝ := x21+x38
  have hx39 : Bounds (3531656529 / 6250000000) (7063313083 / 12500000000) x39 := by
    apply bounds_add hx21 hx38 <;> norm_num
  let x40 : ℝ := x21-x37
  have hx40 : Bounds (3531656529 / 6250000000) (7063313083 / 12500000000) x40 := by
    exact hx39
  let x41 : ℝ := biasE (99 / 200)
  have hx41 : Bounds (3531656529 / 6250000000) (7063313083 / 12500000000) x41 := by
    simpa +zetaDelta only [biasE, div_one] using hx40
  let x42 : ℝ := biasE a
  have hx42 : Bounds (14113043007 / 25000000000) (7063313083 / 12500000000) x42 := by
    exact bounds_biasE ha (by norm_num) (by norm_num) hx20.1 hx41.2
  let x43 : ℝ := a*z
  have hx43 : Bounds (0 / 1) (31 / 62500) x43 := by
    apply bounds_mul ha hz <;> norm_num
  let x44 : ℝ := Real.log (2 / 1)
  have hx44 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x44 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x45 : ℝ := (1 / 1)+(31 / 62500)
  have hx45 : Bounds (62531 / 62500) (62531 / 62500) x45 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((31 / 62500) : ℝ)) <;> norm_num
  let x46 : ℝ := (1 / 1)+(31 / 62500)
  have hx46 : Bounds (62531 / 62500) (62531 / 62500) x46 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((31 / 62500) : ℝ)) <;> norm_num
  let x47 : ℝ := Real.log x46
  have hx47 : Bounds (495877 / 1000000000) (247939 / 500000000) x47 := by
    exact bounds_log hx46 (by norm_num) (by simpa only [div_one] using reflection_log_12486.1) (by simpa only [div_one] using reflection_log_12486.2)
  let x48 : ℝ := x45*x47
  have hx48 : Bounds (248061477 / 500000000000) (124030989 / 250000000000) x48 := by
    apply bounds_mul hx45 hx47 <;> norm_num
  let x49 : ℝ := -(31 / 62500)
  have hx49 : Bounds (-31 / 62500) (-31 / 62500) x49 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((31 / 62500) : ℝ))
  let x50 : ℝ := (1 / 1)+x49
  have hx50 : Bounds (62469 / 62500) (62469 / 62500) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx49 <;> norm_num
  let x51 : ℝ := (1 / 1)-(31 / 62500)
  have hx51 : Bounds (62469 / 62500) (62469 / 62500) x51 := by
    exact hx50
  let x52 : ℝ := -(31 / 62500)
  have hx52 : Bounds (-31 / 62500) (-31 / 62500) x52 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((31 / 62500) : ℝ))
  let x53 : ℝ := (1 / 1)+x52
  have hx53 : Bounds (62469 / 62500) (62469 / 62500) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx52 <;> norm_num
  let x54 : ℝ := (1 / 1)-(31 / 62500)
  have hx54 : Bounds (62469 / 62500) (62469 / 62500) x54 := by
    exact hx53
  let x55 : ℝ := Real.log x54
  have hx55 : Bounds (-124031 / 250000000) (-496123 / 1000000000) x55 := by
    exact bounds_log hx54 (by norm_num) (by simpa only [div_one] using reflection_log_12487.1) (by simpa only [div_one] using reflection_log_12487.2)
  let x56 : ℝ := x51*x55
  have hx56 : Bounds (-495877923 / 1000000000000) (-247938461 / 500000000000) x56 := by
    apply bounds_mul hx51 hx55 <;> norm_num
  let x57 : ℝ := x48+x56
  have hx57 : Bounds (245031 / 1000000000000) (123517 / 500000000000) x57 := by
    apply bounds_add hx48 hx56 <;> norm_num
  let x58 : ℝ := (2 / 1)⁻¹
  have hx58 : Bounds (1 / 2) (1 / 2) x58 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x59 : ℝ := x57*x58
  have hx59 : Bounds (24503 / 200000000000) (123517 / 1000000000000) x59 := by
    apply bounds_mul hx57 hx58 <;> norm_num
  let x60 : ℝ := x57/(2 / 1)
  have hx60 : Bounds (24503 / 200000000000) (123517 / 1000000000000) x60 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx59
  let x61 : ℝ := -x60
  have hx61 : Bounds (-123517 / 1000000000000) (-24503 / 200000000000) x61 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx60
  let x62 : ℝ := x44+x61
  have hx62 : Bounds (693147056483 / 1000000000000) (138629411697 / 200000000000) x62 := by
    apply bounds_add hx44 hx61 <;> norm_num
  let x63 : ℝ := x44-x60
  have hx63 : Bounds (693147056483 / 1000000000000) (138629411697 / 200000000000) x63 := by
    exact hx62
  let x64 : ℝ := biasE (31 / 62500)
  have hx64 : Bounds (693147056483 / 1000000000000) (138629411697 / 200000000000) x64 := by
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
  have hx86 : Bounds (693147056483 / 1000000000000) (693147181 / 1000000000) x86 := by
    exact bounds_biasE hx43 (by norm_num) (by norm_num) hx64.1 hx85.2
  let x87 : ℝ := x42+x86
  have hx87 : Bounds (1257668776763 / 1000000000000) (31455305691 / 25000000000) x87 := by
    apply bounds_add hx42 hx86 <;> norm_num
  let x88 : ℝ := (2 / 1)⁻¹
  have hx88 : Bounds (1 / 2) (1 / 2) x88 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x89 : ℝ := x87*x88
  have hx89 : Bounds (628834388381 / 1000000000000) (31455305691 / 50000000000) x89 := by
    apply bounds_mul hx87 hx88 <;> norm_num
  let x90 : ℝ := x87/(2 / 1)
  have hx90 : Bounds (628834388381 / 1000000000000) (31455305691 / 50000000000) x90 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx89
  let x91 : ℝ := s⁻¹
  have hx91 : Bounds (4028229834681 / 1000000000000) (4044448488893 / 1000000000000) x91 := by
    apply bounds_inv hs <;> norm_num
  let x92 : ℝ := x90*x91
  have hx92 : Bounds (2533089444349 / 1000000000000) (2544387271393 / 1000000000000) x92 := by
    apply bounds_mul hx90 hx91 <;> norm_num
  let x93 : ℝ := x90/s
  have hx93 : Bounds (2533089444349 / 1000000000000) (2544387271393 / 1000000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(6477 / 25000)
  have hx95 : Bounds (31477 / 25000) (31477 / 25000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((6477 / 25000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(6477 / 25000)
  have hx96 : Bounds (31477 / 25000) (31477 / 25000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((6477 / 25000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (46076259 / 200000000) (14398831 / 62500000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_12488.1) (by simpa only [div_one] using reflection_log_12488.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (72517120227 / 250000000000) (36258560271 / 125000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(6477 / 25000)
  have hx99 : Bounds (-6477 / 25000) (-6477 / 25000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((6477 / 25000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (18523 / 25000) (18523 / 25000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(6477 / 25000)
  have hx101 : Bounds (18523 / 25000) (18523 / 25000) x101 := by
    exact hx100
  let x102 : ℝ := -(6477 / 25000)
  have hx102 : Bounds (-6477 / 25000) (-6477 / 25000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((6477 / 25000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (18523 / 25000) (18523 / 25000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(6477 / 25000)
  have hx104 : Bounds (18523 / 25000) (18523 / 25000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-149931311 / 500000000) (-299862621 / 1000000000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_12489.1) (by simpa only [div_one] using reflection_log_12489.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-222174213893 / 1000000000000) (-222174213151 / 1000000000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (13578853403 / 200000000000) (67894269017 / 1000000000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (33947133507 / 1000000000000) (33947134509 / 1000000000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (33947133507 / 1000000000000) (33947134509 / 1000000000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-33947134509 / 1000000000000) (-33947133507 / 1000000000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (659200045491 / 1000000000000) (659200047493 / 1000000000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (659200045491 / 1000000000000) (659200047493 / 1000000000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (6477 / 25000)
  have hx114 : Bounds (659200045491 / 1000000000000) (659200047493 / 1000000000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(130063 / 500000)
  have hx116 : Bounds (630063 / 500000) (630063 / 500000) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((130063 / 500000) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(130063 / 500000)
  have hx117 : Bounds (630063 / 500000) (630063 / 500000) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((130063 / 500000) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (46242343 / 200000000) (57802929 / 250000000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_12490.1) (by simpa only [div_one] using reflection_log_12490.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (36419486697 / 125000000000) (291355894837 / 1000000000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(130063 / 500000)
  have hx120 : Bounds (-130063 / 500000) (-130063 / 500000) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((130063 / 500000) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (369937 / 500000) (369937 / 500000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(130063 / 500000)
  have hx122 : Bounds (369937 / 500000) (369937 / 500000) x122 := by
    exact hx121
  let x123 : ℝ := -(130063 / 500000)
  have hx123 : Bounds (-130063 / 500000) (-130063 / 500000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((130063 / 500000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (369937 / 500000) (369937 / 500000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(130063 / 500000)
  have hx125 : Bounds (369937 / 500000) (369937 / 500000) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-150637689 / 500000000) (-301275377 / 1000000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_12491.1) (by simpa only [div_one] using reflection_log_12491.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-222905819023 / 1000000000000) (-111452909141 / 500000000000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (68450074553 / 1000000000000) (13690015311 / 200000000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (8556259319 / 250000000000) (17112519139 / 500000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (8556259319 / 250000000000) (17112519139 / 500000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-17112519139 / 500000000000) (-8556259319 / 250000000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (329461070861 / 500000000000) (164730535931 / 250000000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (329461070861 / 500000000000) (164730535931 / 250000000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (130063 / 500000)
  have hx135 : Bounds (329461070861 / 500000000000) (164730535931 / 250000000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(6477 / 25000)
  have hx136 : Bounds (656272813241 / 1000000000000) (659199854273 / 1000000000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((6477 / 25000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(130063 / 500000)
  have hx137 : Bounds (823653031 / 1250000000) (661861283359 / 1000000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((130063 / 500000) : ℝ)) <;> norm_num
  have hc : Bounds (6477 / 25000) (130063 / 500000) c := by
    apply contact_bracket hc0 hc1 (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x93 by linarith [hx93.1])
      (show biasE c = x93*c by simpa +zetaDelta only [div_one] using heq)
    · have h1 : x93*(6477 / 25000) ≤ (659199854273 / 1000000000000) := hx136.2
      have h2 : (659200045491 / 1000000000000) ≤ biasE (6477 / 25000) := hx114.1
      linarith
    · have h1 : biasE (130063 / 500000) ≤ (164730535931 / 250000000000) := hx135.2
      have h2 : (823653031 / 1250000000) ≤ x93*(130063 / 500000) := hx137.1
      linarith
  let x138 : ℝ := Real.log (2 / 1)
  have hx138 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x138 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x139 : ℝ := (1 / 1)+(130063 / 500000)
  have hx139 : Bounds (630063 / 500000) (630063 / 500000) x139 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((130063 / 500000) : ℝ)) <;> norm_num
  let x140 : ℝ := (1 / 1)+(130063 / 500000)
  have hx140 : Bounds (630063 / 500000) (630063 / 500000) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((130063 / 500000) : ℝ)) <;> norm_num
  let x141 : ℝ := Real.log x140
  have hx141 : Bounds (46242343 / 200000000) (57802929 / 250000000) x141 := by
    exact bounds_log hx140 (by norm_num) (by simpa only [div_one] using reflection_log_12490.1) (by simpa only [div_one] using reflection_log_12490.2)
  let x142 : ℝ := x139*x141
  have hx142 : Bounds (36419486697 / 125000000000) (291355894837 / 1000000000000) x142 := by
    apply bounds_mul hx139 hx141 <;> norm_num
  let x143 : ℝ := -(130063 / 500000)
  have hx143 : Bounds (-130063 / 500000) (-130063 / 500000) x143 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((130063 / 500000) : ℝ))
  let x144 : ℝ := (1 / 1)+x143
  have hx144 : Bounds (369937 / 500000) (369937 / 500000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx143 <;> norm_num
  let x145 : ℝ := (1 / 1)-(130063 / 500000)
  have hx145 : Bounds (369937 / 500000) (369937 / 500000) x145 := by
    exact hx144
  let x146 : ℝ := -(130063 / 500000)
  have hx146 : Bounds (-130063 / 500000) (-130063 / 500000) x146 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((130063 / 500000) : ℝ))
  let x147 : ℝ := (1 / 1)+x146
  have hx147 : Bounds (369937 / 500000) (369937 / 500000) x147 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx146 <;> norm_num
  let x148 : ℝ := (1 / 1)-(130063 / 500000)
  have hx148 : Bounds (369937 / 500000) (369937 / 500000) x148 := by
    exact hx147
  let x149 : ℝ := Real.log x148
  have hx149 : Bounds (-150637689 / 500000000) (-301275377 / 1000000000) x149 := by
    exact bounds_log hx148 (by norm_num) (by simpa only [div_one] using reflection_log_12491.1) (by simpa only [div_one] using reflection_log_12491.2)
  let x150 : ℝ := x145*x149
  have hx150 : Bounds (-222905819023 / 1000000000000) (-111452909141 / 500000000000) x150 := by
    apply bounds_mul hx145 hx149 <;> norm_num
  let x151 : ℝ := x142+x150
  have hx151 : Bounds (68450074553 / 1000000000000) (13690015311 / 200000000000) x151 := by
    apply bounds_add hx142 hx150 <;> norm_num
  let x152 : ℝ := (2 / 1)⁻¹
  have hx152 : Bounds (1 / 2) (1 / 2) x152 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x153 : ℝ := x151*x152
  have hx153 : Bounds (8556259319 / 250000000000) (17112519139 / 500000000000) x153 := by
    apply bounds_mul hx151 hx152 <;> norm_num
  let x154 : ℝ := x151/(2 / 1)
  have hx154 : Bounds (8556259319 / 250000000000) (17112519139 / 500000000000) x154 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx153
  let x155 : ℝ := -x154
  have hx155 : Bounds (-17112519139 / 500000000000) (-8556259319 / 250000000000) x155 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx154
  let x156 : ℝ := x138+x155
  have hx156 : Bounds (329461070861 / 500000000000) (164730535931 / 250000000000) x156 := by
    apply bounds_add hx138 hx155 <;> norm_num
  let x157 : ℝ := x138-x154
  have hx157 : Bounds (329461070861 / 500000000000) (164730535931 / 250000000000) x157 := by
    exact hx156
  let x158 : ℝ := biasE (130063 / 500000)
  have hx158 : Bounds (329461070861 / 500000000000) (164730535931 / 250000000000) x158 := by
    simpa +zetaDelta only [biasE, div_one] using hx157
  let x159 : ℝ := Real.log (2 / 1)
  have hx159 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x159 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x160 : ℝ := (1 / 1)+(6477 / 25000)
  have hx160 : Bounds (31477 / 25000) (31477 / 25000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((6477 / 25000) : ℝ)) <;> norm_num
  let x161 : ℝ := (1 / 1)+(6477 / 25000)
  have hx161 : Bounds (31477 / 25000) (31477 / 25000) x161 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((6477 / 25000) : ℝ)) <;> norm_num
  let x162 : ℝ := Real.log x161
  have hx162 : Bounds (46076259 / 200000000) (14398831 / 62500000) x162 := by
    exact bounds_log hx161 (by norm_num) (by simpa only [div_one] using reflection_log_12488.1) (by simpa only [div_one] using reflection_log_12488.2)
  let x163 : ℝ := x160*x162
  have hx163 : Bounds (72517120227 / 250000000000) (36258560271 / 125000000000) x163 := by
    apply bounds_mul hx160 hx162 <;> norm_num
  let x164 : ℝ := -(6477 / 25000)
  have hx164 : Bounds (-6477 / 25000) (-6477 / 25000) x164 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((6477 / 25000) : ℝ))
  let x165 : ℝ := (1 / 1)+x164
  have hx165 : Bounds (18523 / 25000) (18523 / 25000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx164 <;> norm_num
  let x166 : ℝ := (1 / 1)-(6477 / 25000)
  have hx166 : Bounds (18523 / 25000) (18523 / 25000) x166 := by
    exact hx165
  let x167 : ℝ := -(6477 / 25000)
  have hx167 : Bounds (-6477 / 25000) (-6477 / 25000) x167 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((6477 / 25000) : ℝ))
  let x168 : ℝ := (1 / 1)+x167
  have hx168 : Bounds (18523 / 25000) (18523 / 25000) x168 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx167 <;> norm_num
  let x169 : ℝ := (1 / 1)-(6477 / 25000)
  have hx169 : Bounds (18523 / 25000) (18523 / 25000) x169 := by
    exact hx168
  let x170 : ℝ := Real.log x169
  have hx170 : Bounds (-149931311 / 500000000) (-299862621 / 1000000000) x170 := by
    exact bounds_log hx169 (by norm_num) (by simpa only [div_one] using reflection_log_12489.1) (by simpa only [div_one] using reflection_log_12489.2)
  let x171 : ℝ := x166*x170
  have hx171 : Bounds (-222174213893 / 1000000000000) (-222174213151 / 1000000000000) x171 := by
    apply bounds_mul hx166 hx170 <;> norm_num
  let x172 : ℝ := x163+x171
  have hx172 : Bounds (13578853403 / 200000000000) (67894269017 / 1000000000000) x172 := by
    apply bounds_add hx163 hx171 <;> norm_num
  let x173 : ℝ := (2 / 1)⁻¹
  have hx173 : Bounds (1 / 2) (1 / 2) x173 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x174 : ℝ := x172*x173
  have hx174 : Bounds (33947133507 / 1000000000000) (33947134509 / 1000000000000) x174 := by
    apply bounds_mul hx172 hx173 <;> norm_num
  let x175 : ℝ := x172/(2 / 1)
  have hx175 : Bounds (33947133507 / 1000000000000) (33947134509 / 1000000000000) x175 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx174
  let x176 : ℝ := -x175
  have hx176 : Bounds (-33947134509 / 1000000000000) (-33947133507 / 1000000000000) x176 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx175
  let x177 : ℝ := x159+x176
  have hx177 : Bounds (659200045491 / 1000000000000) (659200047493 / 1000000000000) x177 := by
    apply bounds_add hx159 hx176 <;> norm_num
  let x178 : ℝ := x159-x175
  have hx178 : Bounds (659200045491 / 1000000000000) (659200047493 / 1000000000000) x178 := by
    exact hx177
  let x179 : ℝ := biasE (6477 / 25000)
  have hx179 : Bounds (659200045491 / 1000000000000) (659200047493 / 1000000000000) x179 := by
    simpa +zetaDelta only [biasE, div_one] using hx178
  let x180 : ℝ := biasE c
  have hx180 : Bounds (329461070861 / 500000000000) (659200047493 / 1000000000000) x180 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx158.1 hx179.2
  let x181 : ℝ := Real.log (2 / 1)
  have hx181 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x181 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x182 : ℝ := c*c
  have hx182 : Bounds (41951529 / 625000000) (16916383969 / 250000000000) x182 := by
    apply bounds_mul hc hc <;> norm_num
  let x183 : ℝ := -x182
  have hx183 : Bounds (-16916383969 / 250000000000) (-41951529 / 625000000) x183 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx182
  let x184 : ℝ := (1 / 1)+x183
  have hx184 : Bounds (233083616031 / 250000000000) (583048471 / 625000000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx183 <;> norm_num
  let x185 : ℝ := (1 / 1)-x182
  have hx185 : Bounds (233083616031 / 250000000000) (583048471 / 625000000) x185 := by
    exact hx184
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (-35031831 / 500000000) (-34740663 / 500000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_12492.1) (by simpa only [div_one] using reflection_log_12493.2)
  let x187 : ℝ := (2 / 1)⁻¹
  have hx187 : Bounds (1 / 2) (1 / 2) x187 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x188 : ℝ := x186*x187
  have hx188 : Bounds (-35031831 / 1000000000) (-34740663 / 1000000000) x188 := by
    apply bounds_mul hx186 hx187 <;> norm_num
  let x189 : ℝ := x186/(2 / 1)
  have hx189 : Bounds (-35031831 / 1000000000) (-34740663 / 1000000000) x189 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx188
  let x190 : ℝ := -x189
  have hx190 : Bounds (34740663 / 1000000000) (35031831 / 1000000000) x190 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx189
  let x191 : ℝ := x181+x190
  have hx191 : Bounds (727887843 / 1000000000) (182044753 / 250000000) x191 := by
    apply bounds_add hx181 hx190 <;> norm_num
  let x192 : ℝ := x181-x189
  have hx192 : Bounds (727887843 / 1000000000) (182044753 / 250000000) x192 := by
    exact hx191
  let x193 : ℝ := c*(1 / 1)
  have hx193 : Bounds (6477 / 25000) (130063 / 500000) x193 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x194 : ℝ := c*x193
  have hx194 : Bounds (41951529 / 625000000) (16916383969 / 250000000000) x194 := by
    apply bounds_mul hc hx193 <;> norm_num
  let x195 : ℝ := c^2
  have hx195 : Bounds (41951529 / 625000000) (16916383969 / 250000000000) x195 := by
    (convert hx194 using 1; ring)
  let x196 : ℝ := -x195
  have hx196 : Bounds (-16916383969 / 250000000000) (-41951529 / 625000000) x196 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx195
  let x197 : ℝ := (1 / 1)+x196
  have hx197 : Bounds (233083616031 / 250000000000) (583048471 / 625000000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx196 <;> norm_num
  let x198 : ℝ := (1 / 1)-x195
  have hx198 : Bounds (233083616031 / 250000000000) (583048471 / 625000000) x198 := by
    exact hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (31477 / 25000) (630063 / 500000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-130063 / 500000) (-6477 / 25000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (369937 / 500000) (18523 / 25000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (369937 / 500000) (18523 / 25000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (674836689521 / 500000000000) (1351581485497 / 1000000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (424836689521 / 250000000000) (851581485497 / 500000000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (424836689521 / 250000000000) (851581485497 / 500000000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (530243917 / 1000000000) (266243547 / 500000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_12494.1) (by simpa only [div_one] using reflection_log_12495.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (530243917 / 2000000000) (266243547 / 1000000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (530243917 / 2000000000) (266243547 / 1000000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (1 / 1)+a
  have hx210 : Bounds (299 / 200) (187 / 125) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) ha <;> norm_num
  let x211 : ℝ := -a
  have hx211 : Bounds (-62 / 125) (-99 / 200) x211 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg ha
  let x212 : ℝ := (1 / 1)+x211
  have hx212 : Bounds (63 / 125) (101 / 200) x212 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx211 <;> norm_num
  let x213 : ℝ := (1 / 1)-a
  have hx213 : Bounds (63 / 125) (101 / 200) x213 := by
    exact hx212
  let x214 : ℝ := x213⁻¹
  have hx214 : Bounds (1980198019801 / 1000000000000) (1984126984127 / 1000000000000) x214 := by
    apply bounds_inv hx213 <;> norm_num
  let x215 : ℝ := x210*x214
  have hx215 : Bounds (1480198019801 / 500000000000) (1484126984127 / 500000000000) x215 := by
    apply bounds_mul hx210 hx214 <;> norm_num
  let x216 : ℝ := x210/x213
  have hx216 : Bounds (1480198019801 / 500000000000) (1484126984127 / 500000000000) x216 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx215
  let x217 : ℝ := Real.log x216
  have hx217 : Bounds (217064611 / 200000000) (1087973891 / 1000000000) x217 := by
    exact bounds_log hx216 (by norm_num) (by simpa only [div_one] using reflection_log_12496.1) (by simpa only [div_one] using reflection_log_12497.2)
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (217064611 / 400000000) (1087973891 / 2000000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (217064611 / 400000000) (1087973891 / 2000000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := (2 / 1)*x192
  have hx221 : Bounds (727887843 / 500000000) (182044753 / 125000000) x221 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x222 : ℝ := c*(1 / 1)
  have hx222 : Bounds (6477 / 25000) (130063 / 500000) x222 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x223 : ℝ := c*x222
  have hx223 : Bounds (41951529 / 625000000) (16916383969 / 250000000000) x223 := by
    apply bounds_mul hc hx222 <;> norm_num
  let x224 : ℝ := c^2
  have hx224 : Bounds (41951529 / 625000000) (16916383969 / 250000000000) x224 := by
    (convert hx223 using 1; ring)
  let x225 : ℝ := -x224
  have hx225 : Bounds (-16916383969 / 250000000000) (-41951529 / 625000000) x225 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx224
  let x226 : ℝ := x221+x225
  have hx226 : Bounds (347027537531 / 250000000000) (217068059 / 156250000) x226 := by
    apply bounds_add hx221 hx225 <;> norm_num
  let x227 : ℝ := x221-x224
  have hx227 : Bounds (347027537531 / 250000000000) (217068059 / 156250000) x227 := by
    exact hx226
  let x228 : ℝ := x180*x227
  have hx228 : Bounds (182931302613 / 200000000000) (915784158733 / 1000000000000) x228 := by
    apply bounds_mul hx180 hx227 <;> norm_num
  let x229 : ℝ := (2 / 1)*x90
  have hx229 : Bounds (628834388381 / 500000000000) (31455305691 / 25000000000) x229 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x230 : ℝ := x198*(1 / 1)
  have hx230 : Bounds (233083616031 / 250000000000) (583048471 / 625000000) x230 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x231 : ℝ := x198*x230
  have hx231 : Bounds (869247552993 / 1000000000000) (870260530011 / 1000000000000) x231 := by
    apply bounds_mul hx198 hx230 <;> norm_num
  let x232 : ℝ := x198^2
  have hx232 : Bounds (869247552993 / 1000000000000) (870260530011 / 1000000000000) x232 := by
    (convert hx231 using 1; ring)
  let x233 : ℝ := x229*x232
  have hx233 : Bounds (273306376669 / 250000000000) (1094972440093 / 1000000000000) x233 := by
    apply bounds_mul hx229 hx232 <;> norm_num
  let x234 : ℝ := x192*(1 / 1)
  have hx234 : Bounds (727887843 / 1000000000) (182044753 / 250000000) x234 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x235 : ℝ := x192*x234
  have hx235 : Bounds (529820711987 / 1000000000000) (265122336759 / 500000000000) x235 := by
    apply bounds_mul hx192 hx234 <;> norm_num
  let x236 : ℝ := x192*x235
  have hx236 : Bounds (48206256903 / 125000000000) (386113042481 / 1000000000000) x236 := by
    apply bounds_mul hx192 hx235 <;> norm_num
  let x237 : ℝ := x192^3
  have hx237 : Bounds (48206256903 / 125000000000) (386113042481 / 1000000000000) x237 := by
    (convert hx236 using 1; ring)
  let x238 : ℝ := x233*x237
  have hx238 : Bounds (421602477021 / 1000000000000) (211391570139 / 500000000000) x238 := by
    apply bounds_mul hx233 hx237 <;> norm_num
  let x239 : ℝ := x238⁻¹
  have hx239 : Bounds (1182639401541 / 500000000000) (2371902572931 / 1000000000000) x239 := by
    apply bounds_inv hx238 <;> norm_num
  let x240 : ℝ := x228*x239
  have hx240 : Bounds (2163417662453 / 1000000000000) (2172150802349 / 1000000000000) x240 := by
    apply bounds_mul hx228 hx239 <;> norm_num
  let x241 : ℝ := x228/x238
  have hx241 : Bounds (2163417662453 / 1000000000000) (2172150802349 / 1000000000000) x241 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx240
  let x242 : ℝ := -x209
  have hx242 : Bounds (-266243547 / 1000000000) (-530243917 / 2000000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x243 : ℝ := (2 / 1)*x192
  have hx243 : Bounds (727887843 / 500000000) (182044753 / 125000000) x243 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x244 : ℝ := c*(1 / 1)
  have hx244 : Bounds (6477 / 25000) (130063 / 500000) x244 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x245 : ℝ := c*x244
  have hx245 : Bounds (41951529 / 625000000) (16916383969 / 250000000000) x245 := by
    apply bounds_mul hc hx244 <;> norm_num
  let x246 : ℝ := c^2
  have hx246 : Bounds (41951529 / 625000000) (16916383969 / 250000000000) x246 := by
    (convert hx245 using 1; ring)
  let x247 : ℝ := -x246
  have hx247 : Bounds (-16916383969 / 250000000000) (-41951529 / 625000000) x247 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx246
  let x248 : ℝ := x243+x247
  have hx248 : Bounds (347027537531 / 250000000000) (217068059 / 156250000) x248 := by
    apply bounds_add hx243 hx247 <;> norm_num
  let x249 : ℝ := x243-x246
  have hx249 : Bounds (347027537531 / 250000000000) (217068059 / 156250000) x249 := by
    exact hx248
  let x250 : ℝ := x242*x249
  have hx250 : Bounds (-369875007799 / 1000000000000) (-184009240807 / 500000000000) x250 := by
    apply bounds_mul hx242 hx249 <;> norm_num
  let x251 : ℝ := x198⁻¹
  have hx251 : Bounds (1071952043589 / 1000000000000) (536288230501 / 500000000000) x251 := by
    apply bounds_inv hx198 <;> norm_num
  let x252 : ℝ := c*x251
  have hx252 : Bounds (277721335453 / 1000000000000) (55801004899 / 200000000000) x252 := by
    apply bounds_mul hc hx251 <;> norm_num
  let x253 : ℝ := c/x198
  have hx253 : Bounds (277721335453 / 1000000000000) (55801004899 / 200000000000) x253 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx252
  let x254 : ℝ := (2 / 1)*x253
  have hx254 : Bounds (277721335453 / 500000000000) (55801004899 / 100000000000) x254 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx253 <;> norm_num
  let x255 : ℝ := (2 / 1)*c
  have hx255 : Bounds (6477 / 12500) (130063 / 250000) x255 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hc <;> norm_num
  let x256 : ℝ := -x255
  have hx256 : Bounds (-130063 / 250000) (-6477 / 12500) x256 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx255
  let x257 : ℝ := x254+x256
  have hx257 : Bounds (17595335453 / 500000000000) (3985004899 / 100000000000) x257 := by
    apply bounds_add hx254 hx256 <;> norm_num
  let x258 : ℝ := x254-x255
  have hx258 : Bounds (17595335453 / 500000000000) (3985004899 / 100000000000) x258 := by
    exact hx257
  let x259 : ℝ := x180*x258
  have hx259 : Bounds (11593956121 / 500000000000) (26269154187 / 1000000000000) x259 := by
    apply bounds_mul hx180 hx258 <;> norm_num
  let x260 : ℝ := x250+x259
  have hx260 : Bounds (-346687095557 / 1000000000000) (-341749327427 / 1000000000000) x260 := by
    apply bounds_add hx250 hx259 <;> norm_num
  let x261 : ℝ := (2 / 1)*x90
  have hx261 : Bounds (628834388381 / 500000000000) (31455305691 / 25000000000) x261 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x262 : ℝ := x198*(1 / 1)
  have hx262 : Bounds (233083616031 / 250000000000) (583048471 / 625000000) x262 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x263 : ℝ := x198*x262
  have hx263 : Bounds (869247552993 / 1000000000000) (870260530011 / 1000000000000) x263 := by
    apply bounds_mul hx198 hx262 <;> norm_num
  let x264 : ℝ := x198^2
  have hx264 : Bounds (869247552993 / 1000000000000) (870260530011 / 1000000000000) x264 := by
    (convert hx263 using 1; ring)
  let x265 : ℝ := x261*x264
  have hx265 : Bounds (273306376669 / 250000000000) (1094972440093 / 1000000000000) x265 := by
    apply bounds_mul hx261 hx264 <;> norm_num
  let x266 : ℝ := x192*(1 / 1)
  have hx266 : Bounds (727887843 / 1000000000) (182044753 / 250000000) x266 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x267 : ℝ := x192*x266
  have hx267 : Bounds (529820711987 / 1000000000000) (265122336759 / 500000000000) x267 := by
    apply bounds_mul hx192 hx266 <;> norm_num
  let x268 : ℝ := x192*x267
  have hx268 : Bounds (48206256903 / 125000000000) (386113042481 / 1000000000000) x268 := by
    apply bounds_mul hx192 hx267 <;> norm_num
  let x269 : ℝ := x192^3
  have hx269 : Bounds (48206256903 / 125000000000) (386113042481 / 1000000000000) x269 := by
    (convert hx268 using 1; ring)
  let x270 : ℝ := x265*x269
  have hx270 : Bounds (421602477021 / 1000000000000) (211391570139 / 500000000000) x270 := by
    apply bounds_mul hx265 hx269 <;> norm_num
  let x271 : ℝ := x270⁻¹
  have hx271 : Bounds (1182639401541 / 500000000000) (2371902572931 / 1000000000000) x271 := by
    apply bounds_inv hx270 <;> norm_num
  let x272 : ℝ := x260*x271
  have hx272 : Bounds (-411154006977 / 500000000000) (-80833244013 / 100000000000) x272 := by
    apply bounds_mul hx260 hx271 <;> norm_num
  let x273 : ℝ := x260/x270
  have hx273 : Bounds (-411154006977 / 500000000000) (-80833244013 / 100000000000) x273 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx272
  let x274 : ℝ := (4 / 1)*c
  have hx274 : Bounds (6477 / 6250) (130063 / 125000) x274 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hc <;> norm_num
  let x275 : ℝ := x198⁻¹
  have hx275 : Bounds (1071952043589 / 1000000000000) (536288230501 / 500000000000) x275 := by
    apply bounds_inv hx198 <;> norm_num
  let x276 : ℝ := x274*x275
  have hx276 : Bounds (277721335453 / 250000000000) (1116020097979 / 1000000000000) x276 := by
    apply bounds_mul hx274 hx275 <;> norm_num
  let x277 : ℝ := x274/x198
  have hx277 : Bounds (277721335453 / 250000000000) (1116020097979 / 1000000000000) x277 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx276
  let x278 : ℝ := (3 / 1)*c
  have hx278 : Bounds (19431 / 25000) (390189 / 500000) x278 := by
    apply bounds_mul (bounds_const ((3 / 1) : ℝ)) hc <;> norm_num
  let x279 : ℝ := x198*x192
  have hx279 : Bounds (135726984409 / 200000000000) (339650927649 / 500000000000) x279 := by
    apply bounds_mul hx198 hx192 <;> norm_num
  let x280 : ℝ := x279⁻¹
  have hx280 : Bounds (147209961551 / 100000000000) (294709266357 / 200000000000) x280 := by
    apply bounds_inv hx279 <;> norm_num
  let x281 : ℝ := x278*x280
  have hx281 : Bounds (572087352579 / 500000000000) (574961569653 / 500000000000) x281 := by
    apply bounds_mul hx278 hx280 <;> norm_num
  let x282 : ℝ := x278/x279
  have hx282 : Bounds (572087352579 / 500000000000) (574961569653 / 500000000000) x282 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx281
  let x283 : ℝ := -x282
  have hx283 : Bounds (-574961569653 / 500000000000) (-572087352579 / 500000000000) x283 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx282
  let x284 : ℝ := x277+x283
  have hx284 : Bounds (-19518898747 / 500000000000) (-28154607179 / 1000000000000) x284 := by
    apply bounds_add hx277 hx283 <;> norm_num
  let x285 : ℝ := x277-x282
  have hx285 : Bounds (-19518898747 / 500000000000) (-28154607179 / 1000000000000) x285 := by
    exact hx284
  let x286 : ℝ := x241*x285
  have hx286 : Bounds (-84795983149 / 1000000000000) (-1218203489 / 20000000000) x286 := by
    apply bounds_mul hx241 hx285 <;> norm_num
  let x287 : ℝ := x273+x286
  have hx287 : Bounds (-907103997103 / 1000000000000) (-43462130729 / 50000000000) x287 := by
    apply bounds_add hx273 hx286 <;> norm_num
  let x288 : ℝ := (2 / 1)*x192
  have hx288 : Bounds (727887843 / 500000000) (182044753 / 125000000) x288 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x289 : ℝ := c*(1 / 1)
  have hx289 : Bounds (6477 / 25000) (130063 / 500000) x289 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x290 : ℝ := c*x289
  have hx290 : Bounds (41951529 / 625000000) (16916383969 / 250000000000) x290 := by
    apply bounds_mul hc hx289 <;> norm_num
  let x291 : ℝ := c^2
  have hx291 : Bounds (41951529 / 625000000) (16916383969 / 250000000000) x291 := by
    (convert hx290 using 1; ring)
  let x292 : ℝ := -x291
  have hx292 : Bounds (-16916383969 / 250000000000) (-41951529 / 625000000) x292 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx291
  let x293 : ℝ := x288+x292
  have hx293 : Bounds (347027537531 / 250000000000) (217068059 / 156250000) x293 := by
    apply bounds_add hx288 hx292 <;> norm_num
  let x294 : ℝ := x288-x291
  have hx294 : Bounds (347027537531 / 250000000000) (217068059 / 156250000) x294 := by
    exact hx293
  let x295 : ℝ := c*x294
  have hx295 : Bounds (179815788847 / 500000000000) (361376293859 / 1000000000000) x295 := by
    apply bounds_mul hc hx294 <;> norm_num
  let x296 : ℝ := x198*(1 / 1)
  have hx296 : Bounds (233083616031 / 250000000000) (583048471 / 625000000) x296 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x297 : ℝ := x198*x296
  have hx297 : Bounds (869247552993 / 1000000000000) (870260530011 / 1000000000000) x297 := by
    apply bounds_mul hx198 hx296 <;> norm_num
  let x298 : ℝ := x198^2
  have hx298 : Bounds (869247552993 / 1000000000000) (870260530011 / 1000000000000) x298 := by
    (convert hx297 using 1; ring)
  let x299 : ℝ := x192*(1 / 1)
  have hx299 : Bounds (727887843 / 1000000000) (182044753 / 250000000) x299 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x300 : ℝ := x192*x299
  have hx300 : Bounds (529820711987 / 1000000000000) (265122336759 / 500000000000) x300 := by
    apply bounds_mul hx192 hx299 <;> norm_num
  let x301 : ℝ := x192^2
  have hx301 : Bounds (529820711987 / 1000000000000) (265122336759 / 500000000000) x301 := by
    (convert hx300 using 1; ring)
  let x302 : ℝ := x298*x301
  have hx302 : Bounds (460545357419 / 1000000000000) (115362752653 / 250000000000) x302 := by
    apply bounds_mul hx298 hx301 <;> norm_num
  let x303 : ℝ := x302⁻¹
  have hx303 : Bounds (2167077277983 / 1000000000000) (434267758383 / 200000000000) x303 := by
    apply bounds_inv hx302 <;> norm_num
  let x304 : ℝ := x295*x303
  have hx304 : Bounds (155869884093 / 200000000000) (156934073067 / 200000000000) x304 := by
    apply bounds_mul hx295 hx303 <;> norm_num
  let x305 : ℝ := x295/x302
  have hx305 : Bounds (155869884093 / 200000000000) (156934073067 / 200000000000) x305 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx304
  let x306 : ℝ := c*x220
  have hx306 : Bounds (68648803 / 488281250) (70752574093 / 500000000000) x306 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x307 : ℝ := x180+x306
  have hx307 : Bounds (399757445133 / 500000000000) (800705195679 / 1000000000000) x307 := by
    apply bounds_add hx180 hx306 <;> norm_num
  let x308 : ℝ := x307*(1 / 1)
  have hx308 : Bounds (399757445133 / 500000000000) (800705195679 / 1000000000000) x308 := by
    apply bounds_mul hx307 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x309 : ℝ := x307*x308
  have hx309 : Bounds (639224059757 / 1000000000000) (160282202597 / 250000000000) x309 := by
    apply bounds_mul hx307 hx308 <;> norm_num
  let x310 : ℝ := x307^2
  have hx310 : Bounds (639224059757 / 1000000000000) (160282202597 / 250000000000) x310 := by
    (convert hx309 using 1; ring)
  let x311 : ℝ := x287*x310
  have hx311 : Bounds (-581570506561 / 1000000000000) (-111128158601 / 200000000000) x311 := by
    apply bounds_mul hx287 hx310 <;> norm_num
  let x312 : ℝ := (2 / 1)*x241
  have hx312 : Bounds (2163417662453 / 500000000000) (2172150802349 / 500000000000) x312 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx241 <;> norm_num
  let x313 : ℝ := c*x220
  have hx313 : Bounds (68648803 / 488281250) (70752574093 / 500000000000) x313 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x314 : ℝ := x180+x313
  have hx314 : Bounds (399757445133 / 500000000000) (800705195679 / 1000000000000) x314 := by
    apply bounds_add hx180 hx313 <;> norm_num
  let x315 : ℝ := x312*x314
  have hx315 : Bounds (3459369269991 / 1000000000000) (3478504866479 / 1000000000000) x315 := by
    apply bounds_mul hx312 hx314 <;> norm_num
  let x316 : ℝ := -x209
  have hx316 : Bounds (-266243547 / 1000000000) (-530243917 / 2000000000) x316 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x317 : ℝ := x220+x316
  have hx317 : Bounds (552835961 / 2000000000) (278864987 / 1000000000) x317 := by
    apply bounds_add hx220 hx316 <;> norm_num
  let x318 : ℝ := x220-x209
  have hx318 : Bounds (552835961 / 2000000000) (278864987 / 1000000000) x318 := by
    exact hx317
  let x319 : ℝ := x315*x318
  have hx319 : Bounds (478115933707 / 500000000000) (970033214371 / 1000000000000) x319 := by
    apply bounds_mul hx315 hx318 <;> norm_num
  let x320 : ℝ := x311+x319
  have hx320 : Bounds (374661360853 / 1000000000000) (207196210683 / 500000000000) x320 := by
    apply bounds_add hx311 hx319 <;> norm_num
  let x321 : ℝ := a*(1 / 1)
  have hx321 : Bounds (99 / 200) (62 / 125) x321 := by
    apply bounds_mul ha (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x322 : ℝ := a*x321
  have hx322 : Bounds (9801 / 40000) (3844 / 15625) x322 := by
    apply bounds_mul ha hx321 <;> norm_num
  let x323 : ℝ := a^2
  have hx323 : Bounds (9801 / 40000) (3844 / 15625) x323 := by
    (convert hx322 using 1; ring)
  let x324 : ℝ := -x323
  have hx324 : Bounds (-3844 / 15625) (-9801 / 40000) x324 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx323
  let x325 : ℝ := (1 / 1)+x324
  have hx325 : Bounds (11781 / 15625) (30199 / 40000) x325 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx324 <;> norm_num
  let x326 : ℝ := (1 / 1)-x323
  have hx326 : Bounds (11781 / 15625) (30199 / 40000) x326 := by
    exact hx325
  let x327 : ℝ := x326⁻¹
  have hx327 : Bounds (331136792609 / 250000000000) (663144045497 / 500000000000) x327 := by
    apply bounds_inv hx326 <;> norm_num
  let x328 : ℝ := (1 / 1)*x327
  have hx328 : Bounds (331136792609 / 250000000000) (663144045497 / 500000000000) x328 := by
    apply bounds_mul (bounds_const ((1 / 1) : ℝ)) hx327 <;> norm_num
  let x329 : ℝ := (1 / 1)/x326
  have hx329 : Bounds (331136792609 / 250000000000) (663144045497 / 500000000000) x329 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx328
  let x330 : ℝ := x329*x305
  have hx330 : Bounds (1032285069657 / 1000000000000) (10406989609 / 10000000000) x330 := by
    apply bounds_mul hx329 hx305 <;> norm_num
  let x331 : ℝ := x320+x330
  have hx331 : Bounds (140694643051 / 100000000000) (727545691133 / 500000000000) x331 := by
    apply bounds_add hx320 hx330 <;> norm_num
  let x332 : ℝ := x180*(1 / 1)
  have hx332 : Bounds (329461070861 / 500000000000) (659200047493 / 1000000000000) x332 := by
    apply bounds_mul hx180 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x333 : ℝ := x180*x332
  have hx333 : Bounds (434178388851 / 1000000000000) (86908940523 / 200000000000) x333 := by
    apply bounds_mul hx180 hx332 <;> norm_num
  let x334 : ℝ := x180^2
  have hx334 : Bounds (434178388851 / 1000000000000) (86908940523 / 200000000000) x334 := by
    (convert hx333 using 1; ring)
  let x335 : ℝ := x331*x334
  have hx335 : Bounds (305432867199 / 500000000000) (126460450397 / 200000000000) x335 := by
    apply bounds_mul hx331 hx334 <;> norm_num
  let x336 : ℝ := x90*x192
  have hx336 : Bounds (228860453281 / 500000000000) (91620373681 / 200000000000) x336 := by
    apply bounds_mul hx90 hx192 <;> norm_num
  let x337 : ℝ := x336⁻¹
  have hx337 : Bounds (3492672941 / 1600000000) (87389497457 / 40000000000) x337 := by
    apply bounds_inv hx336 <;> norm_num
  let x338 : ℝ := x335*x337
  have hx338 : Bounds (1333471388197 / 1000000000000) (172676800131 / 125000000000) x338 := by
    apply bounds_mul hx335 hx337 <;> norm_num
  let x339 : ℝ := x335/x336
  have hx339 : Bounds (1333471388197 / 1000000000000) (172676800131 / 125000000000) x339 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx338
  have hu : x339 < (355477719285426127731 / 227994900250000000000) := lt_of_le_of_lt hx339.2 (by norm_num)
  simpa +zetaDelta only [ScFormula,Kprime,K,Mprime,SmallMean.A,biasB,div_one,pow_two] using hu

open GeneralCK.Reflection
/-- Uniform derivative enclosure including input boxes with z=0. -/
theorem derivative_bound_895 {a z s : ℝ}
    (ha : a ∈ Set.Icc ((99 / 200):ℝ) ((62 / 125)))
    (hz : z ∈ Set.Icc (0:ℝ) (1/1000))
    (hs : s ∈ Set.Ioo (a*(1-z)/2) (a*(1+z)/2)) :
    P a ((biasE a+biasE (a*z))/2) s ≤ (355477719285426127731 / 227994900250000000000) := by
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
  have hsl : (98901 / 400000) ≤ s := by
    have h := mul_le_mul ha.1 (show (999/1000:ℝ) ≤ 1-z by linarith [hz.2])
      (by norm_num : (0:ℝ) ≤ 999/1000) ha0.le
    nlinarith [hs.1]
  have hsu : s ≤ (31031 / 125000) := by
    have h := mul_le_mul ha.2 (show 1+z ≤ (1001/1000:ℝ) by linarith [hz.2])
      (by linarith [hz.1] : 0 ≤ 1+z) (by norm_num : (0:ℝ) ≤ (62 / 125))
    nlinarith [hs.2]
  have hy := div_pos he hs0
  have hc := biasContact_mem hy
  have heq : biasE (biasContact (((biasE a+biasE (a*z))/2)/s)) =
      (((biasE a+biasE (a*z))/2)/s)*biasContact (((biasE a+biasE (a*z))/2)/s) := by
    exact (div_eq_iff hc.1.ne').mp (biasR_biasContact hy)
  have hb := derivative_leaf_895 a z s _ ha hz ⟨hsl,hsu⟩ hc.1.le hc.2.le heq
  rw [P_eq_formula ha0 ha1 he hs0]
  exact hb.le

/-- Checked low-ratio strip: includes arbitrarily small positive z. -/
theorem curvature_leaf_895 {a z : ℝ}
    (ha : a ∈ Set.Icc ((99 / 200):ℝ) ((62 / 125)))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < curvature a (a*z) := by
  have ha0 : 0 < a := by linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  apply curvature_pos_of_derivative_bound ha0 ha1 hz.1 (by linarith [hz.2])
    (fun s hs => derivative_bound_895 ha ⟨hz.1.le,hz.2⟩ hs) (M := (355477719285426127731 / 227994900250000000000))
  exact lt_of_lt_of_le (by norm_num : (355477719285426127731 / 227994900250000000000) < 2*((99 / 200):ℝ)/(1-((99 / 200):ℝ)^2)^2)
    (base_mono (by norm_num) ha.1 ha1)

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Cell0896 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
theorem derivative_leaf_896 (a z s c : ℝ)
    (ha : Bounds (62 / 125) (497 / 1000) a) (hz : Bounds 0 (1/1000) z)
    (hs : Bounds (30969 / 125000) (497497 / 2000000) s) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (heq : biasE c = (((biasE a+biasE (a*z))/2)/s)*c) :
    ScFormula c a ((biasE a+biasE (a*z))/2)*(biasE c)^2 /
      (((biasE a+biasE (a*z))/2)*biasB c) < (434592964977841267229 / 277583922000000000000) := by
  let x0 : ℝ := Real.log (2 / 1)
  have hx0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x0 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x1 : ℝ := (1 / 1)+(497 / 1000)
  have hx1 : Bounds (1497 / 1000) (1497 / 1000) x1 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((497 / 1000) : ℝ)) <;> norm_num
  let x2 : ℝ := (1 / 1)+(497 / 1000)
  have hx2 : Bounds (1497 / 1000) (1497 / 1000) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((497 / 1000) : ℝ)) <;> norm_num
  let x3 : ℝ := Real.log x2
  have hx3 : Bounds (80692621 / 200000000) (201731553 / 500000000) x3 := by
    exact bounds_log hx2 (by norm_num) (by simpa only [div_one] using reflection_log_12498.1) (by simpa only [div_one] using reflection_log_12498.2)
  let x4 : ℝ := x1*x3
  have hx4 : Bounds (120796853637 / 200000000000) (301992134841 / 500000000000) x4 := by
    apply bounds_mul hx1 hx3 <;> norm_num
  let x5 : ℝ := -(497 / 1000)
  have hx5 : Bounds (-497 / 1000) (-497 / 1000) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((497 / 1000) : ℝ))
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (503 / 1000) (503 / 1000) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-(497 / 1000)
  have hx7 : Bounds (503 / 1000) (503 / 1000) x7 := by
    exact hx6
  let x8 : ℝ := -(497 / 1000)
  have hx8 : Bounds (-497 / 1000) (-497 / 1000) x8 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((497 / 1000) : ℝ))
  let x9 : ℝ := (1 / 1)+x8
  have hx9 : Bounds (503 / 1000) (503 / 1000) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx8 <;> norm_num
  let x10 : ℝ := (1 / 1)-(497 / 1000)
  have hx10 : Bounds (503 / 1000) (503 / 1000) x10 := by
    exact hx9
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (-687165109 / 1000000000) (-171791277 / 250000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_12499.1) (by simpa only [div_one] using reflection_log_12499.2)
  let x12 : ℝ := x7*x11
  have hx12 : Bounds (-345644049827 / 1000000000000) (-86411012331 / 250000000000) x12 := by
    apply bounds_mul hx7 hx11 <;> norm_num
  let x13 : ℝ := x4+x12
  have hx13 : Bounds (129170109179 / 500000000000) (129170110179 / 500000000000) x13 := by
    apply bounds_add hx4 hx12 <;> norm_num
  let x14 : ℝ := (2 / 1)⁻¹
  have hx14 : Bounds (1 / 2) (1 / 2) x14 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x15 : ℝ := x13*x14
  have hx15 : Bounds (129170109179 / 1000000000000) (129170110179 / 1000000000000) x15 := by
    apply bounds_mul hx13 hx14 <;> norm_num
  let x16 : ℝ := x13/(2 / 1)
  have hx16 : Bounds (129170109179 / 1000000000000) (129170110179 / 1000000000000) x16 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx15
  let x17 : ℝ := -x16
  have hx17 : Bounds (-129170110179 / 1000000000000) (-129170109179 / 1000000000000) x17 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx16
  let x18 : ℝ := x0+x17
  have hx18 : Bounds (563977069821 / 1000000000000) (563977071821 / 1000000000000) x18 := by
    apply bounds_add hx0 hx17 <;> norm_num
  let x19 : ℝ := x0-x16
  have hx19 : Bounds (563977069821 / 1000000000000) (563977071821 / 1000000000000) x19 := by
    exact hx18
  let x20 : ℝ := biasE (497 / 1000)
  have hx20 : Bounds (563977069821 / 1000000000000) (563977071821 / 1000000000000) x20 := by
    simpa +zetaDelta only [biasE, div_one] using hx19
  let x21 : ℝ := Real.log (2 / 1)
  have hx21 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x21 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x22 : ℝ := (1 / 1)+(62 / 125)
  have hx22 : Bounds (187 / 125) (187 / 125) x22 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((62 / 125) : ℝ)) <;> norm_num
  let x23 : ℝ := (1 / 1)+(62 / 125)
  have hx23 : Bounds (187 / 125) (187 / 125) x23 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((62 / 125) : ℝ)) <;> norm_num
  let x24 : ℝ := Real.log x23
  have hx24 : Bounds (402794879 / 1000000000) (629367 / 1562500) x24 := by
    exact bounds_log hx23 (by norm_num) (by simpa only [div_one] using reflection_log_12484.1) (by simpa only [div_one] using reflection_log_12484.2)
  let x25 : ℝ := x22*x24
  have hx25 : Bounds (75322642373 / 125000000000) (117691629 / 195312500) x25 := by
    apply bounds_mul hx22 hx24 <;> norm_num
  let x26 : ℝ := -(62 / 125)
  have hx26 : Bounds (-62 / 125) (-62 / 125) x26 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((62 / 125) : ℝ))
  let x27 : ℝ := (1 / 1)+x26
  have hx27 : Bounds (63 / 125) (63 / 125) x27 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx26 <;> norm_num
  let x28 : ℝ := (1 / 1)-(62 / 125)
  have hx28 : Bounds (63 / 125) (63 / 125) x28 := by
    exact hx27
  let x29 : ℝ := -(62 / 125)
  have hx29 : Bounds (-62 / 125) (-62 / 125) x29 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((62 / 125) : ℝ))
  let x30 : ℝ := (1 / 1)+x29
  have hx30 : Bounds (63 / 125) (63 / 125) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx29 <;> norm_num
  let x31 : ℝ := (1 / 1)-(62 / 125)
  have hx31 : Bounds (63 / 125) (63 / 125) x31 := by
    exact hx30
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (-685179011 / 1000000000) (-68517901 / 100000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_12485.1) (by simpa only [div_one] using reflection_log_12485.2)
  let x33 : ℝ := x28*x32
  have hx33 : Bounds (-43166277693 / 125000000000) (-4316627763 / 12500000000) x33 := by
    apply bounds_mul hx28 hx32 <;> norm_num
  let x34 : ℝ := x25+x33
  have hx34 : Bounds (803909117 / 3125000000) (3215636493 / 12500000000) x34 := by
    apply bounds_add hx25 hx33 <;> norm_num
  let x35 : ℝ := (2 / 1)⁻¹
  have hx35 : Bounds (1 / 2) (1 / 2) x35 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x36 : ℝ := x34*x35
  have hx36 : Bounds (803909117 / 6250000000) (3215636493 / 25000000000) x36 := by
    apply bounds_mul hx34 hx35 <;> norm_num
  let x37 : ℝ := x34/(2 / 1)
  have hx37 : Bounds (803909117 / 6250000000) (3215636493 / 25000000000) x37 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx36
  let x38 : ℝ := -x37
  have hx38 : Bounds (-3215636493 / 25000000000) (-803909117 / 6250000000) x38 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx37
  let x39 : ℝ := x21+x38
  have hx39 : Bounds (14113043007 / 25000000000) (14113043057 / 25000000000) x39 := by
    apply bounds_add hx21 hx38 <;> norm_num
  let x40 : ℝ := x21-x37
  have hx40 : Bounds (14113043007 / 25000000000) (14113043057 / 25000000000) x40 := by
    exact hx39
  let x41 : ℝ := biasE (62 / 125)
  have hx41 : Bounds (14113043007 / 25000000000) (14113043057 / 25000000000) x41 := by
    simpa +zetaDelta only [biasE, div_one] using hx40
  let x42 : ℝ := biasE a
  have hx42 : Bounds (563977069821 / 1000000000000) (14113043057 / 25000000000) x42 := by
    exact bounds_biasE ha (by norm_num) (by norm_num) hx20.1 hx41.2
  let x43 : ℝ := a*z
  have hx43 : Bounds (0 / 1) (497 / 1000000) x43 := by
    apply bounds_mul ha hz <;> norm_num
  let x44 : ℝ := Real.log (2 / 1)
  have hx44 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x44 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x45 : ℝ := (1 / 1)+(497 / 1000000)
  have hx45 : Bounds (1000497 / 1000000) (1000497 / 1000000) x45 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((497 / 1000000) : ℝ)) <;> norm_num
  let x46 : ℝ := (1 / 1)+(497 / 1000000)
  have hx46 : Bounds (1000497 / 1000000) (1000497 / 1000000) x46 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((497 / 1000000) : ℝ)) <;> norm_num
  let x47 : ℝ := Real.log x46
  have hx47 : Bounds (124219 / 250000000) (496877 / 1000000000) x47 := by
    exact bounds_log hx46 (by norm_num) (by simpa only [div_one] using reflection_log_12500.1) (by simpa only [div_one] using reflection_log_12500.2)
  let x48 : ℝ := x45*x47
  have hx48 : Bounds (497122947 / 1000000000000) (124280987 / 250000000000) x48 := by
    apply bounds_mul hx45 hx47 <;> norm_num
  let x49 : ℝ := -(497 / 1000000)
  have hx49 : Bounds (-497 / 1000000) (-497 / 1000000) x49 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((497 / 1000000) : ℝ))
  let x50 : ℝ := (1 / 1)+x49
  have hx50 : Bounds (999503 / 1000000) (999503 / 1000000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx49 <;> norm_num
  let x51 : ℝ := (1 / 1)-(497 / 1000000)
  have hx51 : Bounds (999503 / 1000000) (999503 / 1000000) x51 := by
    exact hx50
  let x52 : ℝ := -(497 / 1000000)
  have hx52 : Bounds (-497 / 1000000) (-497 / 1000000) x52 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((497 / 1000000) : ℝ))
  let x53 : ℝ := (1 / 1)+x52
  have hx53 : Bounds (999503 / 1000000) (999503 / 1000000) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx52 <;> norm_num
  let x54 : ℝ := (1 / 1)-(497 / 1000000)
  have hx54 : Bounds (999503 / 1000000) (999503 / 1000000) x54 := by
    exact hx53
  let x55 : ℝ := Real.log x54
  have hx55 : Bounds (-124281 / 250000000) (-497123 / 1000000000) x55 := by
    exact bounds_log hx54 (by norm_num) (by simpa only [div_one] using reflection_log_12501.1) (by simpa only [div_one] using reflection_log_12501.2)
  let x56 : ℝ := x51*x55
  have hx56 : Bounds (-49687693 / 100000000000) (-496875929 / 1000000000000) x56 := by
    apply bounds_mul hx51 hx55 <;> norm_num
  let x57 : ℝ := x48+x56
  have hx57 : Bounds (246017 / 1000000000000) (248019 / 1000000000000) x57 := by
    apply bounds_add hx48 hx56 <;> norm_num
  let x58 : ℝ := (2 / 1)⁻¹
  have hx58 : Bounds (1 / 2) (1 / 2) x58 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x59 : ℝ := x57*x58
  have hx59 : Bounds (961 / 7812500000) (12401 / 100000000000) x59 := by
    apply bounds_mul hx57 hx58 <;> norm_num
  let x60 : ℝ := x57/(2 / 1)
  have hx60 : Bounds (961 / 7812500000) (12401 / 100000000000) x60 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx59
  let x61 : ℝ := -x60
  have hx61 : Bounds (-12401 / 100000000000) (-961 / 7812500000) x61 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx60
  let x62 : ℝ := x44+x61
  have hx62 : Bounds (69314705599 / 100000000000) (86643382249 / 125000000000) x62 := by
    apply bounds_add hx44 hx61 <;> norm_num
  let x63 : ℝ := x44-x60
  have hx63 : Bounds (69314705599 / 100000000000) (86643382249 / 125000000000) x63 := by
    exact hx62
  let x64 : ℝ := biasE (497 / 1000000)
  have hx64 : Bounds (69314705599 / 100000000000) (86643382249 / 125000000000) x64 := by
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
  have hx86 : Bounds (69314705599 / 100000000000) (693147181 / 1000000000) x86 := by
    exact bounds_biasE hx43 (by norm_num) (by norm_num) hx64.1 hx85.2
  let x87 : ℝ := x42+x86
  have hx87 : Bounds (1257124125811 / 1000000000000) (15720861291 / 12500000000) x87 := by
    apply bounds_add hx42 hx86 <;> norm_num
  let x88 : ℝ := (2 / 1)⁻¹
  have hx88 : Bounds (1 / 2) (1 / 2) x88 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x89 : ℝ := x87*x88
  have hx89 : Bounds (125712412581 / 200000000000) (15720861291 / 25000000000) x89 := by
    apply bounds_mul hx87 hx88 <;> norm_num
  let x90 : ℝ := x87/(2 / 1)
  have hx90 : Bounds (125712412581 / 200000000000) (15720861291 / 25000000000) x90 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx89
  let x91 : ℝ := s⁻¹
  have hx91 : Bounds (402012474447 / 100000000000) (1009073589719 / 250000000000) x91 := by
    apply bounds_inv hs <;> norm_num
  let x92 : ℝ := x90*x91
  have hx92 : Bounds (2526897902519 / 1000000000000) (1269080474911 / 500000000000) x92 := by
    apply bounds_mul hx90 hx91 <;> norm_num
  let x93 : ℝ := x90/s
  have hx93 : Bounds (2526897902519 / 1000000000000) (1269080474911 / 500000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(51931 / 200000)
  have hx95 : Bounds (251931 / 200000) (251931 / 200000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((51931 / 200000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(51931 / 200000)
  have hx96 : Bounds (251931 / 200000) (251931 / 200000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((51931 / 200000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (230837873 / 1000000000) (115418937 / 500000000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_12502.1) (by simpa only [div_one] using reflection_log_12502.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (290776080913 / 1000000000000) (145388041087 / 500000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(51931 / 200000)
  have hx99 : Bounds (-51931 / 200000) (-51931 / 200000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((51931 / 200000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (148069 / 200000) (148069 / 200000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(51931 / 200000)
  have hx101 : Bounds (148069 / 200000) (148069 / 200000) x101 := by
    exact hx100
  let x102 : ℝ := -(51931 / 200000)
  have hx102 : Bounds (-51931 / 200000) (-51931 / 200000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((51931 / 200000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (148069 / 200000) (148069 / 200000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(51931 / 200000)
  have hx104 : Bounds (148069 / 200000) (148069 / 200000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-150319493 / 500000000) (-60127797 / 200000000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_12503.1) (by simpa only [div_one] using reflection_log_12503.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-222576570091 / 1000000000000) (-222576569349 / 1000000000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (34099755411 / 500000000000) (2727980513 / 40000000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (34099755411 / 1000000000000) (34099756413 / 1000000000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (34099755411 / 1000000000000) (34099756413 / 1000000000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-34099756413 / 1000000000000) (-34099755411 / 1000000000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (659047423587 / 1000000000000) (659047425589 / 1000000000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (659047423587 / 1000000000000) (659047425589 / 1000000000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (51931 / 200000)
  have hx114 : Bounds (659047423587 / 1000000000000) (659047425589 / 1000000000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(260703 / 1000000)
  have hx116 : Bounds (1260703 / 1000000) (1260703 / 1000000) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((260703 / 1000000) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(260703 / 1000000)
  have hx117 : Bounds (1260703 / 1000000) (1260703 / 1000000) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((260703 / 1000000) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (231669501 / 1000000000) (115834751 / 500000000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_12504.1) (by simpa only [div_one] using reflection_log_12504.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (292066434919 / 1000000000000) (14603321809 / 50000000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(260703 / 1000000)
  have hx120 : Bounds (-260703 / 1000000) (-260703 / 1000000) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((260703 / 1000000) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (739297 / 1000000) (739297 / 1000000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(260703 / 1000000)
  have hx122 : Bounds (739297 / 1000000) (739297 / 1000000) x122 := by
    exact hx121
  let x123 : ℝ := -(260703 / 1000000)
  have hx123 : Bounds (-260703 / 1000000) (-260703 / 1000000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((260703 / 1000000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (739297 / 1000000) (739297 / 1000000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(260703 / 1000000)
  have hx125 : Bounds (739297 / 1000000) (739297 / 1000000) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-60411109 / 200000000) (-37756943 / 125000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_12505.1) (by simpa only [div_one] using reflection_log_12505.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-55827189563 / 250000000000) (-27913594689 / 125000000000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (68757676667 / 1000000000000) (17189419667 / 250000000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (34378838333 / 1000000000000) (17189419667 / 500000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (34378838333 / 1000000000000) (17189419667 / 500000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-17189419667 / 500000000000) (-34378838333 / 1000000000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (329384170333 / 500000000000) (658768342667 / 1000000000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (329384170333 / 500000000000) (658768342667 / 1000000000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (260703 / 1000000)
  have hx135 : Bounds (329384170333 / 500000000000) (658768342667 / 1000000000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(51931 / 200000)
  have hx136 : Bounds (328060837439 / 500000000000) (659046181427 / 1000000000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((51931 / 200000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(260703 / 1000000)
  have hx137 : Bounds (16469246597 / 25000000000) (330853087051 / 500000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((260703 / 1000000) : ℝ)) <;> norm_num
  have hc : Bounds (51931 / 200000) (260703 / 1000000) c := by
    apply contact_bracket hc0 hc1 (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x93 by linarith [hx93.1])
      (show biasE c = x93*c by simpa +zetaDelta only [div_one] using heq)
    · have h1 : x93*(51931 / 200000) ≤ (659046181427 / 1000000000000) := hx136.2
      have h2 : (659047423587 / 1000000000000) ≤ biasE (51931 / 200000) := hx114.1
      linarith
    · have h1 : biasE (260703 / 1000000) ≤ (658768342667 / 1000000000000) := hx135.2
      have h2 : (16469246597 / 25000000000) ≤ x93*(260703 / 1000000) := hx137.1
      linarith
  let x138 : ℝ := Real.log (2 / 1)
  have hx138 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x138 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x139 : ℝ := (1 / 1)+(260703 / 1000000)
  have hx139 : Bounds (1260703 / 1000000) (1260703 / 1000000) x139 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((260703 / 1000000) : ℝ)) <;> norm_num
  let x140 : ℝ := (1 / 1)+(260703 / 1000000)
  have hx140 : Bounds (1260703 / 1000000) (1260703 / 1000000) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((260703 / 1000000) : ℝ)) <;> norm_num
  let x141 : ℝ := Real.log x140
  have hx141 : Bounds (231669501 / 1000000000) (115834751 / 500000000) x141 := by
    exact bounds_log hx140 (by norm_num) (by simpa only [div_one] using reflection_log_12504.1) (by simpa only [div_one] using reflection_log_12504.2)
  let x142 : ℝ := x139*x141
  have hx142 : Bounds (292066434919 / 1000000000000) (14603321809 / 50000000000) x142 := by
    apply bounds_mul hx139 hx141 <;> norm_num
  let x143 : ℝ := -(260703 / 1000000)
  have hx143 : Bounds (-260703 / 1000000) (-260703 / 1000000) x143 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((260703 / 1000000) : ℝ))
  let x144 : ℝ := (1 / 1)+x143
  have hx144 : Bounds (739297 / 1000000) (739297 / 1000000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx143 <;> norm_num
  let x145 : ℝ := (1 / 1)-(260703 / 1000000)
  have hx145 : Bounds (739297 / 1000000) (739297 / 1000000) x145 := by
    exact hx144
  let x146 : ℝ := -(260703 / 1000000)
  have hx146 : Bounds (-260703 / 1000000) (-260703 / 1000000) x146 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((260703 / 1000000) : ℝ))
  let x147 : ℝ := (1 / 1)+x146
  have hx147 : Bounds (739297 / 1000000) (739297 / 1000000) x147 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx146 <;> norm_num
  let x148 : ℝ := (1 / 1)-(260703 / 1000000)
  have hx148 : Bounds (739297 / 1000000) (739297 / 1000000) x148 := by
    exact hx147
  let x149 : ℝ := Real.log x148
  have hx149 : Bounds (-60411109 / 200000000) (-37756943 / 125000000) x149 := by
    exact bounds_log hx148 (by norm_num) (by simpa only [div_one] using reflection_log_12505.1) (by simpa only [div_one] using reflection_log_12505.2)
  let x150 : ℝ := x145*x149
  have hx150 : Bounds (-55827189563 / 250000000000) (-27913594689 / 125000000000) x150 := by
    apply bounds_mul hx145 hx149 <;> norm_num
  let x151 : ℝ := x142+x150
  have hx151 : Bounds (68757676667 / 1000000000000) (17189419667 / 250000000000) x151 := by
    apply bounds_add hx142 hx150 <;> norm_num
  let x152 : ℝ := (2 / 1)⁻¹
  have hx152 : Bounds (1 / 2) (1 / 2) x152 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x153 : ℝ := x151*x152
  have hx153 : Bounds (34378838333 / 1000000000000) (17189419667 / 500000000000) x153 := by
    apply bounds_mul hx151 hx152 <;> norm_num
  let x154 : ℝ := x151/(2 / 1)
  have hx154 : Bounds (34378838333 / 1000000000000) (17189419667 / 500000000000) x154 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx153
  let x155 : ℝ := -x154
  have hx155 : Bounds (-17189419667 / 500000000000) (-34378838333 / 1000000000000) x155 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx154
  let x156 : ℝ := x138+x155
  have hx156 : Bounds (329384170333 / 500000000000) (658768342667 / 1000000000000) x156 := by
    apply bounds_add hx138 hx155 <;> norm_num
  let x157 : ℝ := x138-x154
  have hx157 : Bounds (329384170333 / 500000000000) (658768342667 / 1000000000000) x157 := by
    exact hx156
  let x158 : ℝ := biasE (260703 / 1000000)
  have hx158 : Bounds (329384170333 / 500000000000) (658768342667 / 1000000000000) x158 := by
    simpa +zetaDelta only [biasE, div_one] using hx157
  let x159 : ℝ := Real.log (2 / 1)
  have hx159 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x159 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x160 : ℝ := (1 / 1)+(51931 / 200000)
  have hx160 : Bounds (251931 / 200000) (251931 / 200000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((51931 / 200000) : ℝ)) <;> norm_num
  let x161 : ℝ := (1 / 1)+(51931 / 200000)
  have hx161 : Bounds (251931 / 200000) (251931 / 200000) x161 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((51931 / 200000) : ℝ)) <;> norm_num
  let x162 : ℝ := Real.log x161
  have hx162 : Bounds (230837873 / 1000000000) (115418937 / 500000000) x162 := by
    exact bounds_log hx161 (by norm_num) (by simpa only [div_one] using reflection_log_12502.1) (by simpa only [div_one] using reflection_log_12502.2)
  let x163 : ℝ := x160*x162
  have hx163 : Bounds (290776080913 / 1000000000000) (145388041087 / 500000000000) x163 := by
    apply bounds_mul hx160 hx162 <;> norm_num
  let x164 : ℝ := -(51931 / 200000)
  have hx164 : Bounds (-51931 / 200000) (-51931 / 200000) x164 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((51931 / 200000) : ℝ))
  let x165 : ℝ := (1 / 1)+x164
  have hx165 : Bounds (148069 / 200000) (148069 / 200000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx164 <;> norm_num
  let x166 : ℝ := (1 / 1)-(51931 / 200000)
  have hx166 : Bounds (148069 / 200000) (148069 / 200000) x166 := by
    exact hx165
  let x167 : ℝ := -(51931 / 200000)
  have hx167 : Bounds (-51931 / 200000) (-51931 / 200000) x167 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((51931 / 200000) : ℝ))
  let x168 : ℝ := (1 / 1)+x167
  have hx168 : Bounds (148069 / 200000) (148069 / 200000) x168 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx167 <;> norm_num
  let x169 : ℝ := (1 / 1)-(51931 / 200000)
  have hx169 : Bounds (148069 / 200000) (148069 / 200000) x169 := by
    exact hx168
  let x170 : ℝ := Real.log x169
  have hx170 : Bounds (-150319493 / 500000000) (-60127797 / 200000000) x170 := by
    exact bounds_log hx169 (by norm_num) (by simpa only [div_one] using reflection_log_12503.1) (by simpa only [div_one] using reflection_log_12503.2)
  let x171 : ℝ := x166*x170
  have hx171 : Bounds (-222576570091 / 1000000000000) (-222576569349 / 1000000000000) x171 := by
    apply bounds_mul hx166 hx170 <;> norm_num
  let x172 : ℝ := x163+x171
  have hx172 : Bounds (34099755411 / 500000000000) (2727980513 / 40000000000) x172 := by
    apply bounds_add hx163 hx171 <;> norm_num
  let x173 : ℝ := (2 / 1)⁻¹
  have hx173 : Bounds (1 / 2) (1 / 2) x173 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x174 : ℝ := x172*x173
  have hx174 : Bounds (34099755411 / 1000000000000) (34099756413 / 1000000000000) x174 := by
    apply bounds_mul hx172 hx173 <;> norm_num
  let x175 : ℝ := x172/(2 / 1)
  have hx175 : Bounds (34099755411 / 1000000000000) (34099756413 / 1000000000000) x175 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx174
  let x176 : ℝ := -x175
  have hx176 : Bounds (-34099756413 / 1000000000000) (-34099755411 / 1000000000000) x176 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx175
  let x177 : ℝ := x159+x176
  have hx177 : Bounds (659047423587 / 1000000000000) (659047425589 / 1000000000000) x177 := by
    apply bounds_add hx159 hx176 <;> norm_num
  let x178 : ℝ := x159-x175
  have hx178 : Bounds (659047423587 / 1000000000000) (659047425589 / 1000000000000) x178 := by
    exact hx177
  let x179 : ℝ := biasE (51931 / 200000)
  have hx179 : Bounds (659047423587 / 1000000000000) (659047425589 / 1000000000000) x179 := by
    simpa +zetaDelta only [biasE, div_one] using hx178
  let x180 : ℝ := biasE c
  have hx180 : Bounds (329384170333 / 500000000000) (659047425589 / 1000000000000) x180 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx158.1 hx179.2
  let x181 : ℝ := Real.log (2 / 1)
  have hx181 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x181 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x182 : ℝ := c*c
  have hx182 : Bounds (2696828761 / 40000000000) (67966054209 / 1000000000000) x182 := by
    apply bounds_mul hc hc <;> norm_num
  let x183 : ℝ := -x182
  have hx183 : Bounds (-67966054209 / 1000000000000) (-2696828761 / 40000000000) x183 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx182
  let x184 : ℝ := (1 / 1)+x183
  have hx184 : Bounds (932033945791 / 1000000000000) (37303171239 / 40000000000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx183 <;> norm_num
  let x185 : ℝ := (1 / 1)-x182
  have hx185 : Bounds (932033945791 / 1000000000000) (37303171239 / 40000000000) x185 := by
    exact hx184
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (-70386043 / 1000000000) (-69801111 / 1000000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_12506.1) (by simpa only [div_one] using reflection_log_12507.2)
  let x187 : ℝ := (2 / 1)⁻¹
  have hx187 : Bounds (1 / 2) (1 / 2) x187 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x188 : ℝ := x186*x187
  have hx188 : Bounds (-70386043 / 2000000000) (-69801111 / 2000000000) x188 := by
    apply bounds_mul hx186 hx187 <;> norm_num
  let x189 : ℝ := x186/(2 / 1)
  have hx189 : Bounds (-70386043 / 2000000000) (-69801111 / 2000000000) x189 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx188
  let x190 : ℝ := -x189
  have hx190 : Bounds (69801111 / 2000000000) (70386043 / 2000000000) x190 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx189
  let x191 : ℝ := x181+x190
  have hx191 : Bounds (1456095471 / 2000000000) (291336081 / 400000000) x191 := by
    apply bounds_add hx181 hx190 <;> norm_num
  let x192 : ℝ := x181-x189
  have hx192 : Bounds (1456095471 / 2000000000) (291336081 / 400000000) x192 := by
    exact hx191
  let x193 : ℝ := c*(1 / 1)
  have hx193 : Bounds (51931 / 200000) (260703 / 1000000) x193 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x194 : ℝ := c*x193
  have hx194 : Bounds (2696828761 / 40000000000) (67966054209 / 1000000000000) x194 := by
    apply bounds_mul hc hx193 <;> norm_num
  let x195 : ℝ := c^2
  have hx195 : Bounds (2696828761 / 40000000000) (67966054209 / 1000000000000) x195 := by
    (convert hx194 using 1; ring)
  let x196 : ℝ := -x195
  have hx196 : Bounds (-67966054209 / 1000000000000) (-2696828761 / 40000000000) x196 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx195
  let x197 : ℝ := (1 / 1)+x196
  have hx197 : Bounds (932033945791 / 1000000000000) (37303171239 / 40000000000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx196 <;> norm_num
  let x198 : ℝ := (1 / 1)-x195
  have hx198 : Bounds (932033945791 / 1000000000000) (37303171239 / 40000000000) x198 := by
    exact hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (251931 / 200000) (1260703 / 1000000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-260703 / 1000000) (-51931 / 200000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (739297 / 1000000) (148069 / 200000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (739297 / 1000000) (148069 / 200000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (1350721623027 / 1000000000000) (135263635589 / 100000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (850721623027 / 500000000000) (85263635589 / 50000000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (850721623027 / 500000000000) (85263635589 / 50000000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (531476859 / 1000000000) (533725047 / 1000000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_12508.1) (by simpa only [div_one] using reflection_log_12509.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (531476859 / 2000000000) (533725047 / 2000000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (531476859 / 2000000000) (533725047 / 2000000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (1 / 1)+a
  have hx210 : Bounds (187 / 125) (1497 / 1000) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) ha <;> norm_num
  let x211 : ℝ := -a
  have hx211 : Bounds (-497 / 1000) (-62 / 125) x211 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg ha
  let x212 : ℝ := (1 / 1)+x211
  have hx212 : Bounds (503 / 1000) (63 / 125) x212 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx211 <;> norm_num
  let x213 : ℝ := (1 / 1)-a
  have hx213 : Bounds (503 / 1000) (63 / 125) x213 := by
    exact hx212
  let x214 : ℝ := x213⁻¹
  have hx214 : Bounds (992063492063 / 500000000000) (1988071570577 / 1000000000000) x214 := by
    apply bounds_inv hx213 <;> norm_num
  let x215 : ℝ := x210*x214
  have hx215 : Bounds (742063492063 / 250000000000) (1488071570577 / 500000000000) x215 := by
    apply bounds_mul hx210 hx214 <;> norm_num
  let x216 : ℝ := x210/x213
  have hx216 : Bounds (742063492063 / 250000000000) (1488071570577 / 500000000000) x216 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx215
  let x217 : ℝ := Real.log x216
  have hx217 : Bounds (1087973889 / 1000000000) (218125643 / 200000000) x217 := by
    exact bounds_log hx216 (by norm_num) (by simpa only [div_one] using reflection_log_12510.1) (by simpa only [div_one] using reflection_log_12511.2)
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (1087973889 / 2000000000) (218125643 / 400000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (1087973889 / 2000000000) (218125643 / 400000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := (2 / 1)*x192
  have hx221 : Bounds (1456095471 / 1000000000) (291336081 / 200000000) x221 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x222 : ℝ := c*(1 / 1)
  have hx222 : Bounds (51931 / 200000) (260703 / 1000000) x222 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x223 : ℝ := c*x222
  have hx223 : Bounds (2696828761 / 40000000000) (67966054209 / 1000000000000) x223 := by
    apply bounds_mul hc hx222 <;> norm_num
  let x224 : ℝ := c^2
  have hx224 : Bounds (2696828761 / 40000000000) (67966054209 / 1000000000000) x224 := by
    (convert hx223 using 1; ring)
  let x225 : ℝ := -x224
  have hx225 : Bounds (-67966054209 / 1000000000000) (-2696828761 / 40000000000) x225 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx224
  let x226 : ℝ := x221+x225
  have hx226 : Bounds (1388129416791 / 1000000000000) (55570387439 / 40000000000) x226 := by
    apply bounds_add hx221 hx225 <;> norm_num
  let x227 : ℝ := x221-x224
  have hx227 : Bounds (1388129416791 / 1000000000000) (55570387439 / 40000000000) x227 := by
    exact hx226
  let x228 : ℝ := x180*x227
  have hx228 : Bounds (914455712529 / 1000000000000) (915588019517 / 1000000000000) x228 := by
    apply bounds_mul hx180 hx227 <;> norm_num
  let x229 : ℝ := (2 / 1)*x90
  have hx229 : Bounds (125712412581 / 100000000000) (15720861291 / 12500000000) x229 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x230 : ℝ := x198*(1 / 1)
  have hx230 : Bounds (932033945791 / 1000000000000) (37303171239 / 40000000000) x230 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x231 : ℝ := x198*x230
  have hx231 : Bounds (434343638053 / 500000000000) (108713014413 / 125000000000) x231 := by
    apply bounds_mul hx198 hx230 <;> norm_num
  let x232 : ℝ := x198^2
  have hx232 : Bounds (434343638053 / 500000000000) (108713014413 / 125000000000) x232 := by
    (convert hx231 using 1; ring)
  let x233 : ℝ := x229*x232
  have hx233 : Bounds (1092047732577 / 1000000000000) (1093799820873 / 1000000000000) x233 := by
    apply bounds_mul hx229 hx232 <;> norm_num
  let x234 : ℝ := x192*(1 / 1)
  have hx234 : Bounds (1456095471 / 2000000000) (291336081 / 400000000) x234 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x235 : ℝ := x192*x234
  have hx235 : Bounds (265026752583 / 500000000000) (265239725289 / 500000000000) x235 := by
    apply bounds_mul hx192 hx234 <;> norm_num
  let x236 : ℝ := x192*x235
  have hx236 : Bounds (385904254129 / 1000000000000) (386369510457 / 1000000000000) x236 := by
    apply bounds_mul hx192 hx235 <;> norm_num
  let x237 : ℝ := x192^3
  have hx237 : Bounds (385904254129 / 1000000000000) (386369510457 / 1000000000000) x237 := by
    (convert hx236 using 1; ring)
  let x238 : ℝ := x233*x237
  have hx238 : Bounds (421425865713 / 1000000000000) (422610901329 / 1000000000000) x238 := by
    apply bounds_mul hx233 hx237 <;> norm_num
  let x239 : ℝ := x238⁻¹
  have hx239 : Bounds (295780349269 / 125000000000) (118644829537 / 50000000000) x239 := by
    apply bounds_inv hx238 <;> norm_num
  let x240 : ℝ := x228*x239
  have hx240 : Bounds (1081912120171 / 500000000000) (434519138007 / 200000000000) x240 := by
    apply bounds_mul hx228 hx239 <;> norm_num
  let x241 : ℝ := x228/x238
  have hx241 : Bounds (1081912120171 / 500000000000) (434519138007 / 200000000000) x241 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx240
  let x242 : ℝ := -x209
  have hx242 : Bounds (-533725047 / 2000000000) (-531476859 / 2000000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x243 : ℝ := (2 / 1)*x192
  have hx243 : Bounds (1456095471 / 1000000000) (291336081 / 200000000) x243 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x244 : ℝ := c*(1 / 1)
  have hx244 : Bounds (51931 / 200000) (260703 / 1000000) x244 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x245 : ℝ := c*x244
  have hx245 : Bounds (2696828761 / 40000000000) (67966054209 / 1000000000000) x245 := by
    apply bounds_mul hc hx244 <;> norm_num
  let x246 : ℝ := c^2
  have hx246 : Bounds (2696828761 / 40000000000) (67966054209 / 1000000000000) x246 := by
    (convert hx245 using 1; ring)
  let x247 : ℝ := -x246
  have hx247 : Bounds (-67966054209 / 1000000000000) (-2696828761 / 40000000000) x247 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx246
  let x248 : ℝ := x243+x247
  have hx248 : Bounds (1388129416791 / 1000000000000) (55570387439 / 40000000000) x248 := by
    apply bounds_add hx243 hx247 <;> norm_num
  let x249 : ℝ := x243-x246
  have hx249 : Bounds (1388129416791 / 1000000000000) (55570387439 / 40000000000) x249 := by
    exact hx248
  let x250 : ℝ := x242*x249
  have hx250 : Bounds (-370741345597 / 1000000000000) (-9221983279 / 25000000000) x250 := by
    apply bounds_mul hx242 hx249 <;> norm_num
  let x251 : ℝ := x198⁻¹
  have hx251 : Bounds (107229489267 / 100000000000) (214584458971 / 200000000000) x251 := by
    apply bounds_inv hx198 <;> norm_num
  let x252 : ℝ := c*x251
  have hx252 : Bounds (69606682589 / 250000000000) (69928515259 / 250000000000) x252 := by
    apply bounds_mul hc hx251 <;> norm_num
  let x253 : ℝ := c/x198
  have hx253 : Bounds (69606682589 / 250000000000) (69928515259 / 250000000000) x253 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx252
  let x254 : ℝ := (2 / 1)*x253
  have hx254 : Bounds (69606682589 / 125000000000) (69928515259 / 125000000000) x254 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx253 <;> norm_num
  let x255 : ℝ := (2 / 1)*c
  have hx255 : Bounds (51931 / 100000) (260703 / 500000) x255 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hc <;> norm_num
  let x256 : ℝ := -x255
  have hx256 : Bounds (-260703 / 500000) (-51931 / 100000) x256 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx255
  let x257 : ℝ := x254+x256
  have hx257 : Bounds (4430932589 / 125000000000) (5014765259 / 125000000000) x257 := by
    apply bounds_add hx254 hx256 <;> norm_num
  let x258 : ℝ := x254-x255
  have hx258 : Bounds (4430932589 / 125000000000) (5014765259 / 125000000000) x258 := by
    exact hx257
  let x259 : ℝ := x180*x258
  have hx259 : Bounds (11675832437 / 500000000000) (1652484067 / 62500000000) x259 := by
    apply bounds_mul hx180 hx258 <;> norm_num
  let x260 : ℝ := x250+x259
  have hx260 : Bounds (-347389680723 / 1000000000000) (-42804948261 / 125000000000) x260 := by
    apply bounds_add hx250 hx259 <;> norm_num
  let x261 : ℝ := (2 / 1)*x90
  have hx261 : Bounds (125712412581 / 100000000000) (15720861291 / 12500000000) x261 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x262 : ℝ := x198*(1 / 1)
  have hx262 : Bounds (932033945791 / 1000000000000) (37303171239 / 40000000000) x262 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x263 : ℝ := x198*x262
  have hx263 : Bounds (434343638053 / 500000000000) (108713014413 / 125000000000) x263 := by
    apply bounds_mul hx198 hx262 <;> norm_num
  let x264 : ℝ := x198^2
  have hx264 : Bounds (434343638053 / 500000000000) (108713014413 / 125000000000) x264 := by
    (convert hx263 using 1; ring)
  let x265 : ℝ := x261*x264
  have hx265 : Bounds (1092047732577 / 1000000000000) (1093799820873 / 1000000000000) x265 := by
    apply bounds_mul hx261 hx264 <;> norm_num
  let x266 : ℝ := x192*(1 / 1)
  have hx266 : Bounds (1456095471 / 2000000000) (291336081 / 400000000) x266 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x267 : ℝ := x192*x266
  have hx267 : Bounds (265026752583 / 500000000000) (265239725289 / 500000000000) x267 := by
    apply bounds_mul hx192 hx266 <;> norm_num
  let x268 : ℝ := x192*x267
  have hx268 : Bounds (385904254129 / 1000000000000) (386369510457 / 1000000000000) x268 := by
    apply bounds_mul hx192 hx267 <;> norm_num
  let x269 : ℝ := x192^3
  have hx269 : Bounds (385904254129 / 1000000000000) (386369510457 / 1000000000000) x269 := by
    (convert hx268 using 1; ring)
  let x270 : ℝ := x265*x269
  have hx270 : Bounds (421425865713 / 1000000000000) (422610901329 / 1000000000000) x270 := by
    apply bounds_mul hx265 hx269 <;> norm_num
  let x271 : ℝ := x270⁻¹
  have hx271 : Bounds (295780349269 / 125000000000) (118644829537 / 50000000000) x271 := by
    apply bounds_inv hx270 <;> norm_num
  let x272 : ℝ := x260*x271
  have hx272 : Bounds (-412159894523 / 500000000000) (-810295203013 / 1000000000000) x272 := by
    apply bounds_mul hx260 hx271 <;> norm_num
  let x273 : ℝ := x260/x270
  have hx273 : Bounds (-412159894523 / 500000000000) (-810295203013 / 1000000000000) x273 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx272
  let x274 : ℝ := (4 / 1)*c
  have hx274 : Bounds (51931 / 50000) (260703 / 250000) x274 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hc <;> norm_num
  let x275 : ℝ := x198⁻¹
  have hx275 : Bounds (107229489267 / 100000000000) (214584458971 / 200000000000) x275 := by
    apply bounds_inv hx198 <;> norm_num
  let x276 : ℝ := x274*x275
  have hx276 : Bounds (69606682589 / 62500000000) (1118856244143 / 1000000000000) x276 := by
    apply bounds_mul hx274 hx275 <;> norm_num
  let x277 : ℝ := x274/x198
  have hx277 : Bounds (69606682589 / 62500000000) (1118856244143 / 1000000000000) x277 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx276
  let x278 : ℝ := (3 / 1)*c
  have hx278 : Bounds (155793 / 200000) (782109 / 1000000) x278 := by
    apply bounds_mul (bounds_const ((3 / 1) : ℝ)) hc <;> norm_num
  let x279 : ℝ := x198*x192
  have hx279 : Bounds (339282601821 / 500000000000) (679234982353 / 1000000000000) x279 := by
    apply bounds_mul hx198 hx192 <;> norm_num
  let x280 : ℝ := x279⁻¹
  have hx280 : Bounds (736122274309 / 500000000000) (1473697729611 / 1000000000000) x280 := by
    apply bounds_inv hx279 <;> norm_num
  let x281 : ℝ := x278*x280
  have hx281 : Bounds (573413487407 / 500000000000) (1152592257609 / 1000000000000) x281 := by
    apply bounds_mul hx278 hx280 <;> norm_num
  let x282 : ℝ := x278/x279
  have hx282 : Bounds (573413487407 / 500000000000) (1152592257609 / 1000000000000) x282 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx281
  let x283 : ℝ := -x282
  have hx283 : Bounds (-1152592257609 / 1000000000000) (-573413487407 / 500000000000) x283 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx282
  let x284 : ℝ := x277+x283
  have hx284 : Bounds (-7777067237 / 200000000000) (-27970730671 / 1000000000000) x284 := by
    apply bounds_add hx277 hx283 <;> norm_num
  let x285 : ℝ := x277-x282
  have hx285 : Bounds (-7777067237 / 200000000000) (-27970730671 / 1000000000000) x285 := by
    exact hx284
  let x286 : ℝ := x241*x285
  have hx286 : Bounds (-42241056901 / 500000000000) (-12104749009 / 200000000000) x286 := by
    apply bounds_mul hx241 hx285 <;> norm_num
  let x287 : ℝ := x273+x286
  have hx287 : Bounds (-3550007433 / 3906250000) (-435409474029 / 500000000000) x287 := by
    apply bounds_add hx273 hx286 <;> norm_num
  let x288 : ℝ := (2 / 1)*x192
  have hx288 : Bounds (1456095471 / 1000000000) (291336081 / 200000000) x288 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x289 : ℝ := c*(1 / 1)
  have hx289 : Bounds (51931 / 200000) (260703 / 1000000) x289 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x290 : ℝ := c*x289
  have hx290 : Bounds (2696828761 / 40000000000) (67966054209 / 1000000000000) x290 := by
    apply bounds_mul hc hx289 <;> norm_num
  let x291 : ℝ := c^2
  have hx291 : Bounds (2696828761 / 40000000000) (67966054209 / 1000000000000) x291 := by
    (convert hx290 using 1; ring)
  let x292 : ℝ := -x291
  have hx292 : Bounds (-67966054209 / 1000000000000) (-2696828761 / 40000000000) x292 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx291
  let x293 : ℝ := x288+x292
  have hx293 : Bounds (1388129416791 / 1000000000000) (55570387439 / 40000000000) x293 := by
    apply bounds_add hx288 hx292 <;> norm_num
  let x294 : ℝ := x288-x291
  have hx294 : Bounds (1388129416791 / 1000000000000) (55570387439 / 40000000000) x294 := by
    exact hx293
  let x295 : ℝ := c*x294
  have hx295 : Bounds (90108685929 / 250000000000) (362184167913 / 1000000000000) x295 := by
    apply bounds_mul hc hx294 <;> norm_num
  let x296 : ℝ := x198*(1 / 1)
  have hx296 : Bounds (932033945791 / 1000000000000) (37303171239 / 40000000000) x296 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x297 : ℝ := x198*x296
  have hx297 : Bounds (434343638053 / 500000000000) (108713014413 / 125000000000) x297 := by
    apply bounds_mul hx198 hx296 <;> norm_num
  let x298 : ℝ := x198^2
  have hx298 : Bounds (434343638053 / 500000000000) (108713014413 / 125000000000) x298 := by
    (convert hx297 using 1; ring)
  let x299 : ℝ := x192*(1 / 1)
  have hx299 : Bounds (1456095471 / 2000000000) (291336081 / 400000000) x299 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x300 : ℝ := x192*x299
  have hx300 : Bounds (265026752583 / 500000000000) (265239725289 / 500000000000) x300 := by
    apply bounds_mul hx192 hx299 <;> norm_num
  let x301 : ℝ := x192^2
  have hx301 : Bounds (265026752583 / 500000000000) (265239725289 / 500000000000) x301 := by
    (convert hx300 using 1; ring)
  let x302 : ℝ := x298*x301
  have hx302 : Bounds (460450735593 / 1000000000000) (115340040313 / 250000000000) x302 := by
    apply bounds_mul hx298 hx301 <;> norm_num
  let x303 : ℝ := x302⁻¹
  have hx303 : Bounds (270938001367 / 125000000000) (2171784998263 / 1000000000000) x303 := by
    apply bounds_inv hx302 <;> norm_num
  let x304 : ℝ := x295*x303
  have hx304 : Bounds (156248750537 / 200000000000) (393293071241 / 500000000000) x304 := by
    apply bounds_mul hx295 hx303 <;> norm_num
  let x305 : ℝ := x295/x302
  have hx305 : Bounds (156248750537 / 200000000000) (393293071241 / 500000000000) x305 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx304
  let x306 : ℝ := c*x220
  have hx306 : Bounds (70624465037 / 500000000000) (17770627971 / 125000000000) x306 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x307 : ℝ := x180+x306
  have hx307 : Bounds (40000863537 / 50000000000) (801212449357 / 1000000000000) x307 := by
    apply bounds_add hx180 hx306 <;> norm_num
  let x308 : ℝ := x307*(1 / 1)
  have hx308 : Bounds (40000863537 / 50000000000) (801212449357 / 1000000000000) x308 := by
    apply bounds_mul hx307 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x309 : ℝ := x307*x308
  have hx309 : Bounds (320013816741 / 500000000000) (128388277801 / 200000000000) x309 := by
    apply bounds_mul hx307 hx308 <;> norm_num
  let x310 : ℝ := x307^2
  have hx310 : Bounds (320013816741 / 500000000000) (128388277801 / 200000000000) x310 := by
    (convert hx309 using 1; ring)
  let x311 : ℝ := x287*x310
  have hx311 : Bounds (-116679511169 / 200000000000) (-139337047629 / 250000000000) x311 := by
    apply bounds_mul hx287 hx310 <;> norm_num
  let x312 : ℝ := (2 / 1)*x241
  have hx312 : Bounds (1081912120171 / 250000000000) (434519138007 / 100000000000) x312 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx241 <;> norm_num
  let x313 : ℝ := c*x220
  have hx313 : Bounds (70624465037 / 500000000000) (17770627971 / 125000000000) x313 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x314 : ℝ := x180+x313
  have hx314 : Bounds (40000863537 / 50000000000) (801212449357 / 1000000000000) x314 := by
    apply bounds_add hx180 hx313 <;> norm_num
  let x315 : ℝ := x312*x314
  have hx315 : Bounds (1731096763119 / 500000000000) (3481421428551 / 1000000000000) x315 := by
    apply bounds_mul hx312 hx314 <;> norm_num
  let x316 : ℝ := -x209
  have hx316 : Bounds (-533725047 / 2000000000) (-531476859 / 2000000000) x316 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x317 : ℝ := x220+x316
  have hx317 : Bounds (277124421 / 1000000000) (139787839 / 500000000) x317 := by
    apply bounds_add hx220 hx316 <;> norm_num
  let x318 : ℝ := x220-x209
  have hx318 : Bounds (277124421 / 1000000000) (139787839 / 500000000) x318 := by
    exact hx317
  let x319 : ℝ := x315*x318
  have hx319 : Bounds (239864594087 / 250000000000) (973320756291 / 1000000000000) x319 := by
    apply bounds_mul hx315 hx318 <;> norm_num
  let x320 : ℝ := x311+x319
  have hx320 : Bounds (376060820503 / 1000000000000) (16638902631 / 40000000000) x320 := by
    apply bounds_add hx311 hx319 <;> norm_num
  let x321 : ℝ := a*(1 / 1)
  have hx321 : Bounds (62 / 125) (497 / 1000) x321 := by
    apply bounds_mul ha (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x322 : ℝ := a*x321
  have hx322 : Bounds (3844 / 15625) (247009 / 1000000) x322 := by
    apply bounds_mul ha hx321 <;> norm_num
  let x323 : ℝ := a^2
  have hx323 : Bounds (3844 / 15625) (247009 / 1000000) x323 := by
    (convert hx322 using 1; ring)
  let x324 : ℝ := -x323
  have hx324 : Bounds (-247009 / 1000000) (-3844 / 15625) x324 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx323
  let x325 : ℝ := (1 / 1)+x324
  have hx325 : Bounds (752991 / 1000000) (11781 / 15625) x325 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx324 <;> norm_num
  let x326 : ℝ := (1 / 1)-x323
  have hx326 : Bounds (752991 / 1000000) (11781 / 15625) x326 := by
    exact hx325
  let x327 : ℝ := x326⁻¹
  have hx327 : Bounds (1326288090993 / 1000000000000) (664018560647 / 500000000000) x327 := by
    apply bounds_inv hx326 <;> norm_num
  let x328 : ℝ := (1 / 1)*x327
  have hx328 : Bounds (1326288090993 / 1000000000000) (664018560647 / 500000000000) x328 := by
    apply bounds_mul (bounds_const ((1 / 1) : ℝ)) hx327 <;> norm_num
  let x329 : ℝ := (1 / 1)/x326
  have hx329 : Bounds (1326288090993 / 1000000000000) (664018560647 / 500000000000) x329 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx328
  let x330 : ℝ := x329*x305
  have hx330 : Bounds (259038571337 / 250000000000) (130576949539 / 125000000000) x330 := by
    apply bounds_mul hx329 hx305 <;> norm_num
  let x331 : ℝ := x320+x330
  have hx331 : Bounds (1412215105851 / 1000000000000) (1460588162087 / 1000000000000) x331 := by
    apply bounds_add hx320 hx330 <;> norm_num
  let x332 : ℝ := x180*(1 / 1)
  have hx332 : Bounds (329384170333 / 500000000000) (659047425589 / 1000000000000) x332 := by
    apply bounds_mul hx180 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x333 : ℝ := x180*x332
  have hx333 : Bounds (433975726663 / 1000000000000) (54292938647 / 125000000000) x333 := by
    apply bounds_mul hx180 hx332 <;> norm_num
  let x334 : ℝ := x180^2
  have hx334 : Bounds (433975726663 / 1000000000000) (54292938647 / 125000000000) x334 := by
    (convert hx333 using 1; ring)
  let x335 : ℝ := x331*x334
  have hx335 : Bounds (306433538383 / 500000000000) (317198493891 / 500000000000) x335 := by
    apply bounds_mul hx331 hx334 <;> norm_num
  let x336 : ℝ := x90*x192
  have hx336 : Bounds (457623186519 / 1000000000000) (458005411847 / 1000000000000) x336 := by
    apply bounds_mul hx90 hx192 <;> norm_num
  let x337 : ℝ := x336⁻¹
  have hx337 : Bounds (545845078537 / 250000000000) (2185203961379 / 1000000000000) x337 := by
    apply bounds_inv hx336 <;> norm_num
  let x338 : ℝ := x335*x337
  have hx338 : Bounds (6690609553 / 5000000000) (1386286810789 / 1000000000000) x338 := by
    apply bounds_mul hx335 hx337 <;> norm_num
  let x339 : ℝ := x335/x336
  have hx339 : Bounds (6690609553 / 5000000000) (1386286810789 / 1000000000000) x339 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx338
  have hu : x339 < (434592964977841267229 / 277583922000000000000) := lt_of_le_of_lt hx339.2 (by norm_num)
  simpa +zetaDelta only [ScFormula,Kprime,K,Mprime,SmallMean.A,biasB,div_one,pow_two] using hu

open GeneralCK.Reflection
/-- Uniform derivative enclosure including input boxes with z=0. -/
theorem derivative_bound_896 {a z s : ℝ}
    (ha : a ∈ Set.Icc ((62 / 125):ℝ) ((497 / 1000)))
    (hz : z ∈ Set.Icc (0:ℝ) (1/1000))
    (hs : s ∈ Set.Ioo (a*(1-z)/2) (a*(1+z)/2)) :
    P a ((biasE a+biasE (a*z))/2) s ≤ (434592964977841267229 / 277583922000000000000) := by
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
  have hsl : (30969 / 125000) ≤ s := by
    have h := mul_le_mul ha.1 (show (999/1000:ℝ) ≤ 1-z by linarith [hz.2])
      (by norm_num : (0:ℝ) ≤ 999/1000) ha0.le
    nlinarith [hs.1]
  have hsu : s ≤ (497497 / 2000000) := by
    have h := mul_le_mul ha.2 (show 1+z ≤ (1001/1000:ℝ) by linarith [hz.2])
      (by linarith [hz.1] : 0 ≤ 1+z) (by norm_num : (0:ℝ) ≤ (497 / 1000))
    nlinarith [hs.2]
  have hy := div_pos he hs0
  have hc := biasContact_mem hy
  have heq : biasE (biasContact (((biasE a+biasE (a*z))/2)/s)) =
      (((biasE a+biasE (a*z))/2)/s)*biasContact (((biasE a+biasE (a*z))/2)/s) := by
    exact (div_eq_iff hc.1.ne').mp (biasR_biasContact hy)
  have hb := derivative_leaf_896 a z s _ ha hz ⟨hsl,hsu⟩ hc.1.le hc.2.le heq
  rw [P_eq_formula ha0 ha1 he hs0]
  exact hb.le

/-- Checked low-ratio strip: includes arbitrarily small positive z. -/
theorem curvature_leaf_896 {a z : ℝ}
    (ha : a ∈ Set.Icc ((62 / 125):ℝ) ((497 / 1000)))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < curvature a (a*z) := by
  have ha0 : 0 < a := by linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  apply curvature_pos_of_derivative_bound ha0 ha1 hz.1 (by linarith [hz.2])
    (fun s hs => derivative_bound_896 ha ⟨hz.1.le,hz.2⟩ hs) (M := (434592964977841267229 / 277583922000000000000))
  exact lt_of_lt_of_le (by norm_num : (434592964977841267229 / 277583922000000000000) < 2*((62 / 125):ℝ)/(1-((62 / 125):ℝ)^2)^2)
    (base_mono (by norm_num) ha.1 ha1)

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Cell0897 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
theorem derivative_leaf_897 (a z s c : ℝ)
    (ha : Bounds (497 / 1000) (249 / 500) a) (hz : Bounds 0 (1/1000) z)
    (hs : Bounds (496503 / 2000000) (249249 / 1000000) s) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (heq : biasE c = (((biasE a+biasE (a*z))/2)/s)*c) :
    ScFormula c a ((biasE a+biasE (a*z))/2)*(biasE c)^2 /
      (((biasE a+biasE (a*z))/2)*biasB c) < (1782780341458166494288249 / 1133990892162000000000000) := by
  let x0 : ℝ := Real.log (2 / 1)
  have hx0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x0 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x1 : ℝ := (1 / 1)+(249 / 500)
  have hx1 : Bounds (749 / 500) (749 / 500) x1 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((249 / 500) : ℝ)) <;> norm_num
  let x2 : ℝ := (1 / 1)+(249 / 500)
  have hx2 : Bounds (749 / 500) (749 / 500) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((249 / 500) : ℝ)) <;> norm_num
  let x3 : ℝ := Real.log x2
  have hx3 : Bounds (80826177 / 200000000) (202065443 / 500000000) x3 := by
    exact bounds_log hx2 (by norm_num) (by simpa only [div_one] using reflection_log_12512.1) (by simpa only [div_one] using reflection_log_12512.2)
  let x4 : ℝ := x1*x3
  have hx4 : Bounds (60538806573 / 100000000000) (151347016807 / 250000000000) x4 := by
    apply bounds_mul hx1 hx3 <;> norm_num
  let x5 : ℝ := -(249 / 500)
  have hx5 : Bounds (-249 / 500) (-249 / 500) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((249 / 500) : ℝ))
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (251 / 500) (251 / 500) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-(249 / 500)
  have hx7 : Bounds (251 / 500) (251 / 500) x7 := by
    exact hx6
  let x8 : ℝ := -(249 / 500)
  have hx8 : Bounds (-249 / 500) (-249 / 500) x8 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((249 / 500) : ℝ))
  let x9 : ℝ := (1 / 1)+x8
  have hx9 : Bounds (251 / 500) (251 / 500) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx8 <;> norm_num
  let x10 : ℝ := (1 / 1)-(249 / 500)
  have hx10 : Bounds (251 / 500) (251 / 500) x10 := by
    exact hx9
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (-17228879 / 25000000) (-689155159 / 1000000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_12513.1) (by simpa only [div_one] using reflection_log_12513.2)
  let x12 : ℝ := x7*x11
  have hx12 : Bounds (-4324448629 / 12500000000) (-172977944909 / 500000000000) x12 := by
    apply bounds_mul hx7 hx11 <;> norm_num
  let x13 : ℝ := x4+x12
  have hx13 : Bounds (25943217541 / 100000000000) (25943217741 / 100000000000) x13 := by
    apply bounds_add hx4 hx12 <;> norm_num
  let x14 : ℝ := (2 / 1)⁻¹
  have hx14 : Bounds (1 / 2) (1 / 2) x14 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x15 : ℝ := x13*x14
  have hx15 : Bounds (25943217541 / 200000000000) (25943217741 / 200000000000) x15 := by
    apply bounds_mul hx13 hx14 <;> norm_num
  let x16 : ℝ := x13/(2 / 1)
  have hx16 : Bounds (25943217541 / 200000000000) (25943217741 / 200000000000) x16 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx15
  let x17 : ℝ := -x16
  have hx17 : Bounds (-25943217741 / 200000000000) (-25943217541 / 200000000000) x17 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx16
  let x18 : ℝ := x0+x17
  have hx18 : Bounds (112686218259 / 200000000000) (112686218659 / 200000000000) x18 := by
    apply bounds_add hx0 hx17 <;> norm_num
  let x19 : ℝ := x0-x16
  have hx19 : Bounds (112686218259 / 200000000000) (112686218659 / 200000000000) x19 := by
    exact hx18
  let x20 : ℝ := biasE (249 / 500)
  have hx20 : Bounds (112686218259 / 200000000000) (112686218659 / 200000000000) x20 := by
    simpa +zetaDelta only [biasE, div_one] using hx19
  let x21 : ℝ := Real.log (2 / 1)
  have hx21 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x21 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x22 : ℝ := (1 / 1)+(497 / 1000)
  have hx22 : Bounds (1497 / 1000) (1497 / 1000) x22 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((497 / 1000) : ℝ)) <;> norm_num
  let x23 : ℝ := (1 / 1)+(497 / 1000)
  have hx23 : Bounds (1497 / 1000) (1497 / 1000) x23 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((497 / 1000) : ℝ)) <;> norm_num
  let x24 : ℝ := Real.log x23
  have hx24 : Bounds (80692621 / 200000000) (201731553 / 500000000) x24 := by
    exact bounds_log hx23 (by norm_num) (by simpa only [div_one] using reflection_log_12498.1) (by simpa only [div_one] using reflection_log_12498.2)
  let x25 : ℝ := x22*x24
  have hx25 : Bounds (120796853637 / 200000000000) (301992134841 / 500000000000) x25 := by
    apply bounds_mul hx22 hx24 <;> norm_num
  let x26 : ℝ := -(497 / 1000)
  have hx26 : Bounds (-497 / 1000) (-497 / 1000) x26 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((497 / 1000) : ℝ))
  let x27 : ℝ := (1 / 1)+x26
  have hx27 : Bounds (503 / 1000) (503 / 1000) x27 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx26 <;> norm_num
  let x28 : ℝ := (1 / 1)-(497 / 1000)
  have hx28 : Bounds (503 / 1000) (503 / 1000) x28 := by
    exact hx27
  let x29 : ℝ := -(497 / 1000)
  have hx29 : Bounds (-497 / 1000) (-497 / 1000) x29 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((497 / 1000) : ℝ))
  let x30 : ℝ := (1 / 1)+x29
  have hx30 : Bounds (503 / 1000) (503 / 1000) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx29 <;> norm_num
  let x31 : ℝ := (1 / 1)-(497 / 1000)
  have hx31 : Bounds (503 / 1000) (503 / 1000) x31 := by
    exact hx30
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (-687165109 / 1000000000) (-171791277 / 250000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_12499.1) (by simpa only [div_one] using reflection_log_12499.2)
  let x33 : ℝ := x28*x32
  have hx33 : Bounds (-345644049827 / 1000000000000) (-86411012331 / 250000000000) x33 := by
    apply bounds_mul hx28 hx32 <;> norm_num
  let x34 : ℝ := x25+x33
  have hx34 : Bounds (129170109179 / 500000000000) (129170110179 / 500000000000) x34 := by
    apply bounds_add hx25 hx33 <;> norm_num
  let x35 : ℝ := (2 / 1)⁻¹
  have hx35 : Bounds (1 / 2) (1 / 2) x35 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x36 : ℝ := x34*x35
  have hx36 : Bounds (129170109179 / 1000000000000) (129170110179 / 1000000000000) x36 := by
    apply bounds_mul hx34 hx35 <;> norm_num
  let x37 : ℝ := x34/(2 / 1)
  have hx37 : Bounds (129170109179 / 1000000000000) (129170110179 / 1000000000000) x37 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx36
  let x38 : ℝ := -x37
  have hx38 : Bounds (-129170110179 / 1000000000000) (-129170109179 / 1000000000000) x38 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx37
  let x39 : ℝ := x21+x38
  have hx39 : Bounds (563977069821 / 1000000000000) (563977071821 / 1000000000000) x39 := by
    apply bounds_add hx21 hx38 <;> norm_num
  let x40 : ℝ := x21-x37
  have hx40 : Bounds (563977069821 / 1000000000000) (563977071821 / 1000000000000) x40 := by
    exact hx39
  let x41 : ℝ := biasE (497 / 1000)
  have hx41 : Bounds (563977069821 / 1000000000000) (563977071821 / 1000000000000) x41 := by
    simpa +zetaDelta only [biasE, div_one] using hx40
  let x42 : ℝ := biasE a
  have hx42 : Bounds (112686218259 / 200000000000) (563977071821 / 1000000000000) x42 := by
    exact bounds_biasE ha (by norm_num) (by norm_num) hx20.1 hx41.2
  let x43 : ℝ := a*z
  have hx43 : Bounds (0 / 1) (249 / 500000) x43 := by
    apply bounds_mul ha hz <;> norm_num
  let x44 : ℝ := Real.log (2 / 1)
  have hx44 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x44 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x45 : ℝ := (1 / 1)+(249 / 500000)
  have hx45 : Bounds (500249 / 500000) (500249 / 500000) x45 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((249 / 500000) : ℝ)) <;> norm_num
  let x46 : ℝ := (1 / 1)+(249 / 500000)
  have hx46 : Bounds (500249 / 500000) (500249 / 500000) x46 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((249 / 500000) : ℝ)) <;> norm_num
  let x47 : ℝ := Real.log x46
  have hx47 : Bounds (124469 / 250000000) (497877 / 1000000000) x47 := by
    exact bounds_log hx46 (by norm_num) (by simpa only [div_one] using reflection_log_12514.1) (by simpa only [div_one] using reflection_log_12514.2)
  let x48 : ℝ := x45*x47
  have hx48 : Bounds (249061971 / 500000000000) (498124943 / 1000000000000) x48 := by
    apply bounds_mul hx45 hx47 <;> norm_num
  let x49 : ℝ := -(249 / 500000)
  have hx49 : Bounds (-249 / 500000) (-249 / 500000) x49 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((249 / 500000) : ℝ))
  let x50 : ℝ := (1 / 1)+x49
  have hx50 : Bounds (499751 / 500000) (499751 / 500000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx49 <;> norm_num
  let x51 : ℝ := (1 / 1)-(249 / 500000)
  have hx51 : Bounds (499751 / 500000) (499751 / 500000) x51 := by
    exact hx50
  let x52 : ℝ := -(249 / 500000)
  have hx52 : Bounds (-249 / 500000) (-249 / 500000) x52 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((249 / 500000) : ℝ))
  let x53 : ℝ := (1 / 1)+x52
  have hx53 : Bounds (499751 / 500000) (499751 / 500000) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx52 <;> norm_num
  let x54 : ℝ := (1 / 1)-(249 / 500000)
  have hx54 : Bounds (499751 / 500000) (499751 / 500000) x54 := by
    exact hx53
  let x55 : ℝ := Real.log x54
  have hx55 : Bounds (-797 / 1600000) (-124531 / 250000000) x55 := by
    exact bounds_log hx54 (by norm_num) (by simpa only [div_one] using reflection_log_12515.1) (by simpa only [div_one] using reflection_log_12515.2)
  let x56 : ℝ := x51*x55
  have hx56 : Bounds (-248938467 / 500000000000) (-248937967 / 500000000000) x56 := by
    apply bounds_mul hx51 hx55 <;> norm_num
  let x57 : ℝ := x48+x56
  have hx57 : Bounds (7719 / 31250000000) (249009 / 1000000000000) x57 := by
    apply bounds_add hx48 hx56 <;> norm_num
  let x58 : ℝ := (2 / 1)⁻¹
  have hx58 : Bounds (1 / 2) (1 / 2) x58 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x59 : ℝ := x57*x58
  have hx59 : Bounds (7719 / 62500000000) (24901 / 200000000000) x59 := by
    apply bounds_mul hx57 hx58 <;> norm_num
  let x60 : ℝ := x57/(2 / 1)
  have hx60 : Bounds (7719 / 62500000000) (24901 / 200000000000) x60 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx59
  let x61 : ℝ := -x60
  have hx61 : Bounds (-24901 / 200000000000) (-7719 / 62500000000) x61 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx60
  let x62 : ℝ := x44+x61
  have hx62 : Bounds (138629411099 / 200000000000) (86643382187 / 125000000000) x62 := by
    apply bounds_add hx44 hx61 <;> norm_num
  let x63 : ℝ := x44-x60
  have hx63 : Bounds (138629411099 / 200000000000) (86643382187 / 125000000000) x63 := by
    exact hx62
  let x64 : ℝ := biasE (249 / 500000)
  have hx64 : Bounds (138629411099 / 200000000000) (86643382187 / 125000000000) x64 := by
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
  have hx86 : Bounds (138629411099 / 200000000000) (693147181 / 1000000000) x86 := by
    exact bounds_biasE hx43 (by norm_num) (by norm_num) hx64.1 hx85.2
  let x87 : ℝ := x42+x86
  have hx87 : Bounds (125657814679 / 100000000000) (1257124252821 / 1000000000000) x87 := by
    apply bounds_add hx42 hx86 <;> norm_num
  let x88 : ℝ := (2 / 1)⁻¹
  have hx88 : Bounds (1 / 2) (1 / 2) x88 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x89 : ℝ := x87*x88
  have hx89 : Bounds (125657814679 / 200000000000) (628562126411 / 1000000000000) x89 := by
    apply bounds_mul hx87 hx88 <;> norm_num
  let x90 : ℝ := x87/(2 / 1)
  have hx90 : Bounds (125657814679 / 200000000000) (628562126411 / 1000000000000) x90 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx89
  let x91 : ℝ := s⁻¹
  have hx91 : Bounds (4012052204823 / 1000000000000) (2014086521129 / 500000000000) x91 := by
    apply bounds_inv hs <;> norm_num
  let x92 : ℝ := x90*x91
  have hx92 : Bounds (126036428109 / 50000000000) (1265978506497 / 500000000000) x92 := by
    apply bounds_mul hx90 hx91 <;> norm_num
  let x93 : ℝ := x90/s
  have hx93 : Bounds (126036428109 / 50000000000) (1265978506497 / 500000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(260231 / 1000000)
  have hx95 : Bounds (1260231 / 1000000) (1260231 / 1000000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((260231 / 1000000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(260231 / 1000000)
  have hx96 : Bounds (1260231 / 1000000) (1260231 / 1000000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((260231 / 1000000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (231295037 / 1000000000) (115647519 / 500000000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_12516.1) (by simpa only [div_one] using reflection_log_12516.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (291485175773 / 1000000000000) (145742588517 / 500000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(260231 / 1000000)
  have hx99 : Bounds (-260231 / 1000000) (-260231 / 1000000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((260231 / 1000000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (739769 / 1000000) (739769 / 1000000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(260231 / 1000000)
  have hx101 : Bounds (739769 / 1000000) (739769 / 1000000) x101 := by
    exact hx100
  let x102 : ℝ := -(260231 / 1000000)
  have hx102 : Bounds (-260231 / 1000000) (-260231 / 1000000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((260231 / 1000000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (739769 / 1000000) (739769 / 1000000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(260231 / 1000000)
  have hx104 : Bounds (739769 / 1000000) (739769 / 1000000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-37677163 / 125000000) (-301417303 / 1000000000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_12517.1) (by simpa only [div_one] using reflection_log_12517.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-222979177563 / 1000000000000) (-222979176823 / 1000000000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (6850599821 / 100000000000) (68506000211 / 1000000000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (6850599821 / 200000000000) (17126500053 / 500000000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (6850599821 / 200000000000) (17126500053 / 500000000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-17126500053 / 500000000000) (-6850599821 / 200000000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (329447089947 / 500000000000) (131778836379 / 200000000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (329447089947 / 500000000000) (131778836379 / 200000000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (260231 / 1000000)
  have hx114 : Bounds (329447089947 / 500000000000) (131778836379 / 200000000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(1633 / 6250)
  have hx116 : Bounds (7883 / 6250) (7883 / 6250) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1633 / 6250) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(1633 / 6250)
  have hx117 : Bounds (7883 / 6250) (7883 / 6250) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1633 / 6250) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (116063539 / 500000000) (232127079 / 1000000000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_12518.1) (by simpa only [div_one] using reflection_log_12518.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (292777240939 / 1000000000000) (146388621101 / 500000000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(1633 / 6250)
  have hx120 : Bounds (-1633 / 6250) (-1633 / 6250) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1633 / 6250) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (4617 / 6250) (4617 / 6250) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(1633 / 6250)
  have hx122 : Bounds (4617 / 6250) (4617 / 6250) x122 := by
    exact hx121
  let x123 : ℝ := -(1633 / 6250)
  have hx123 : Bounds (-1633 / 6250) (-1633 / 6250) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1633 / 6250) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (4617 / 6250) (4617 / 6250) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(1633 / 6250)
  have hx125 : Bounds (4617 / 6250) (4617 / 6250) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-302836321 / 1000000000) (-1892727 / 6250000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_12519.1) (by simpa only [div_one] using reflection_log_12519.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-4474224941 / 20000000000) (-22371124631 / 100000000000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (69065993889 / 1000000000000) (17266498973 / 250000000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (2158312309 / 62500000000) (17266498973 / 500000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (2158312309 / 62500000000) (17266498973 / 500000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-17266498973 / 500000000000) (-2158312309 / 62500000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (329307091027 / 500000000000) (82326773007 / 125000000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (329307091027 / 500000000000) (82326773007 / 125000000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (1633 / 6250)
  have hx135 : Bounds (329307091027 / 500000000000) (82326773007 / 125000000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(260231 / 1000000)
  have hx136 : Bounds (20499116077 / 31250000000) (658893705449 / 1000000000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((260231 / 1000000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(1633 / 6250)
  have hx137 : Bounds (329307979363 / 500000000000) (165387432089 / 250000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((1633 / 6250) : ℝ)) <;> norm_num
  have hc : Bounds (260231 / 1000000) (1633 / 6250) c := by
    apply contact_bracket hc0 hc1 (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x93 by linarith [hx93.1])
      (show biasE c = x93*c by simpa +zetaDelta only [div_one] using heq)
    · have h1 : x93*(260231 / 1000000) ≤ (658893705449 / 1000000000000) := hx136.2
      have h2 : (329447089947 / 500000000000) ≤ biasE (260231 / 1000000) := hx114.1
      linarith
    · have h1 : biasE (1633 / 6250) ≤ (82326773007 / 125000000000) := hx135.2
      have h2 : (329307979363 / 500000000000) ≤ x93*(1633 / 6250) := hx137.1
      linarith
  let x138 : ℝ := Real.log (2 / 1)
  have hx138 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x138 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x139 : ℝ := (1 / 1)+(1633 / 6250)
  have hx139 : Bounds (7883 / 6250) (7883 / 6250) x139 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1633 / 6250) : ℝ)) <;> norm_num
  let x140 : ℝ := (1 / 1)+(1633 / 6250)
  have hx140 : Bounds (7883 / 6250) (7883 / 6250) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1633 / 6250) : ℝ)) <;> norm_num
  let x141 : ℝ := Real.log x140
  have hx141 : Bounds (116063539 / 500000000) (232127079 / 1000000000) x141 := by
    exact bounds_log hx140 (by norm_num) (by simpa only [div_one] using reflection_log_12518.1) (by simpa only [div_one] using reflection_log_12518.2)
  let x142 : ℝ := x139*x141
  have hx142 : Bounds (292777240939 / 1000000000000) (146388621101 / 500000000000) x142 := by
    apply bounds_mul hx139 hx141 <;> norm_num
  let x143 : ℝ := -(1633 / 6250)
  have hx143 : Bounds (-1633 / 6250) (-1633 / 6250) x143 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1633 / 6250) : ℝ))
  let x144 : ℝ := (1 / 1)+x143
  have hx144 : Bounds (4617 / 6250) (4617 / 6250) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx143 <;> norm_num
  let x145 : ℝ := (1 / 1)-(1633 / 6250)
  have hx145 : Bounds (4617 / 6250) (4617 / 6250) x145 := by
    exact hx144
  let x146 : ℝ := -(1633 / 6250)
  have hx146 : Bounds (-1633 / 6250) (-1633 / 6250) x146 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1633 / 6250) : ℝ))
  let x147 : ℝ := (1 / 1)+x146
  have hx147 : Bounds (4617 / 6250) (4617 / 6250) x147 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx146 <;> norm_num
  let x148 : ℝ := (1 / 1)-(1633 / 6250)
  have hx148 : Bounds (4617 / 6250) (4617 / 6250) x148 := by
    exact hx147
  let x149 : ℝ := Real.log x148
  have hx149 : Bounds (-302836321 / 1000000000) (-1892727 / 6250000) x149 := by
    exact bounds_log hx148 (by norm_num) (by simpa only [div_one] using reflection_log_12519.1) (by simpa only [div_one] using reflection_log_12519.2)
  let x150 : ℝ := x145*x149
  have hx150 : Bounds (-4474224941 / 20000000000) (-22371124631 / 100000000000) x150 := by
    apply bounds_mul hx145 hx149 <;> norm_num
  let x151 : ℝ := x142+x150
  have hx151 : Bounds (69065993889 / 1000000000000) (17266498973 / 250000000000) x151 := by
    apply bounds_add hx142 hx150 <;> norm_num
  let x152 : ℝ := (2 / 1)⁻¹
  have hx152 : Bounds (1 / 2) (1 / 2) x152 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x153 : ℝ := x151*x152
  have hx153 : Bounds (2158312309 / 62500000000) (17266498973 / 500000000000) x153 := by
    apply bounds_mul hx151 hx152 <;> norm_num
  let x154 : ℝ := x151/(2 / 1)
  have hx154 : Bounds (2158312309 / 62500000000) (17266498973 / 500000000000) x154 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx153
  let x155 : ℝ := -x154
  have hx155 : Bounds (-17266498973 / 500000000000) (-2158312309 / 62500000000) x155 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx154
  let x156 : ℝ := x138+x155
  have hx156 : Bounds (329307091027 / 500000000000) (82326773007 / 125000000000) x156 := by
    apply bounds_add hx138 hx155 <;> norm_num
  let x157 : ℝ := x138-x154
  have hx157 : Bounds (329307091027 / 500000000000) (82326773007 / 125000000000) x157 := by
    exact hx156
  let x158 : ℝ := biasE (1633 / 6250)
  have hx158 : Bounds (329307091027 / 500000000000) (82326773007 / 125000000000) x158 := by
    simpa +zetaDelta only [biasE, div_one] using hx157
  let x159 : ℝ := Real.log (2 / 1)
  have hx159 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x159 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x160 : ℝ := (1 / 1)+(260231 / 1000000)
  have hx160 : Bounds (1260231 / 1000000) (1260231 / 1000000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((260231 / 1000000) : ℝ)) <;> norm_num
  let x161 : ℝ := (1 / 1)+(260231 / 1000000)
  have hx161 : Bounds (1260231 / 1000000) (1260231 / 1000000) x161 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((260231 / 1000000) : ℝ)) <;> norm_num
  let x162 : ℝ := Real.log x161
  have hx162 : Bounds (231295037 / 1000000000) (115647519 / 500000000) x162 := by
    exact bounds_log hx161 (by norm_num) (by simpa only [div_one] using reflection_log_12516.1) (by simpa only [div_one] using reflection_log_12516.2)
  let x163 : ℝ := x160*x162
  have hx163 : Bounds (291485175773 / 1000000000000) (145742588517 / 500000000000) x163 := by
    apply bounds_mul hx160 hx162 <;> norm_num
  let x164 : ℝ := -(260231 / 1000000)
  have hx164 : Bounds (-260231 / 1000000) (-260231 / 1000000) x164 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((260231 / 1000000) : ℝ))
  let x165 : ℝ := (1 / 1)+x164
  have hx165 : Bounds (739769 / 1000000) (739769 / 1000000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx164 <;> norm_num
  let x166 : ℝ := (1 / 1)-(260231 / 1000000)
  have hx166 : Bounds (739769 / 1000000) (739769 / 1000000) x166 := by
    exact hx165
  let x167 : ℝ := -(260231 / 1000000)
  have hx167 : Bounds (-260231 / 1000000) (-260231 / 1000000) x167 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((260231 / 1000000) : ℝ))
  let x168 : ℝ := (1 / 1)+x167
  have hx168 : Bounds (739769 / 1000000) (739769 / 1000000) x168 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx167 <;> norm_num
  let x169 : ℝ := (1 / 1)-(260231 / 1000000)
  have hx169 : Bounds (739769 / 1000000) (739769 / 1000000) x169 := by
    exact hx168
  let x170 : ℝ := Real.log x169
  have hx170 : Bounds (-37677163 / 125000000) (-301417303 / 1000000000) x170 := by
    exact bounds_log hx169 (by norm_num) (by simpa only [div_one] using reflection_log_12517.1) (by simpa only [div_one] using reflection_log_12517.2)
  let x171 : ℝ := x166*x170
  have hx171 : Bounds (-222979177563 / 1000000000000) (-222979176823 / 1000000000000) x171 := by
    apply bounds_mul hx166 hx170 <;> norm_num
  let x172 : ℝ := x163+x171
  have hx172 : Bounds (6850599821 / 100000000000) (68506000211 / 1000000000000) x172 := by
    apply bounds_add hx163 hx171 <;> norm_num
  let x173 : ℝ := (2 / 1)⁻¹
  have hx173 : Bounds (1 / 2) (1 / 2) x173 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x174 : ℝ := x172*x173
  have hx174 : Bounds (6850599821 / 200000000000) (17126500053 / 500000000000) x174 := by
    apply bounds_mul hx172 hx173 <;> norm_num
  let x175 : ℝ := x172/(2 / 1)
  have hx175 : Bounds (6850599821 / 200000000000) (17126500053 / 500000000000) x175 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx174
  let x176 : ℝ := -x175
  have hx176 : Bounds (-17126500053 / 500000000000) (-6850599821 / 200000000000) x176 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx175
  let x177 : ℝ := x159+x176
  have hx177 : Bounds (329447089947 / 500000000000) (131778836379 / 200000000000) x177 := by
    apply bounds_add hx159 hx176 <;> norm_num
  let x178 : ℝ := x159-x175
  have hx178 : Bounds (329447089947 / 500000000000) (131778836379 / 200000000000) x178 := by
    exact hx177
  let x179 : ℝ := biasE (260231 / 1000000)
  have hx179 : Bounds (329447089947 / 500000000000) (131778836379 / 200000000000) x179 := by
    simpa +zetaDelta only [biasE, div_one] using hx178
  let x180 : ℝ := biasE c
  have hx180 : Bounds (329307091027 / 500000000000) (131778836379 / 200000000000) x180 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx158.1 hx179.2
  let x181 : ℝ := Real.log (2 / 1)
  have hx181 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x181 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x182 : ℝ := c*c
  have hx182 : Bounds (67720173361 / 1000000000000) (2666689 / 39062500) x182 := by
    apply bounds_mul hc hc <;> norm_num
  let x183 : ℝ := -x182
  have hx183 : Bounds (-2666689 / 39062500) (-67720173361 / 1000000000000) x183 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx182
  let x184 : ℝ := (1 / 1)+x183
  have hx184 : Bounds (36395811 / 39062500) (932279826639 / 1000000000000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx183 <;> norm_num
  let x185 : ℝ := (1 / 1)-x182
  have hx185 : Bounds (36395811 / 39062500) (932279826639 / 1000000000000) x185 := by
    exact hx184
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (-35354621 / 500000000) (-35061133 / 500000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_12520.1) (by simpa only [div_one] using reflection_log_12521.2)
  let x187 : ℝ := (2 / 1)⁻¹
  have hx187 : Bounds (1 / 2) (1 / 2) x187 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x188 : ℝ := x186*x187
  have hx188 : Bounds (-35354621 / 1000000000) (-35061133 / 1000000000) x188 := by
    apply bounds_mul hx186 hx187 <;> norm_num
  let x189 : ℝ := x186/(2 / 1)
  have hx189 : Bounds (-35354621 / 1000000000) (-35061133 / 1000000000) x189 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx188
  let x190 : ℝ := -x189
  have hx190 : Bounds (35061133 / 1000000000) (35354621 / 1000000000) x190 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx189
  let x191 : ℝ := x181+x190
  have hx191 : Bounds (728208313 / 1000000000) (364250901 / 500000000) x191 := by
    apply bounds_add hx181 hx190 <;> norm_num
  let x192 : ℝ := x181-x189
  have hx192 : Bounds (728208313 / 1000000000) (364250901 / 500000000) x192 := by
    exact hx191
  let x193 : ℝ := c*(1 / 1)
  have hx193 : Bounds (260231 / 1000000) (1633 / 6250) x193 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x194 : ℝ := c*x193
  have hx194 : Bounds (67720173361 / 1000000000000) (2666689 / 39062500) x194 := by
    apply bounds_mul hc hx193 <;> norm_num
  let x195 : ℝ := c^2
  have hx195 : Bounds (67720173361 / 1000000000000) (2666689 / 39062500) x195 := by
    (convert hx194 using 1; ring)
  let x196 : ℝ := -x195
  have hx196 : Bounds (-2666689 / 39062500) (-67720173361 / 1000000000000) x196 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx195
  let x197 : ℝ := (1 / 1)+x196
  have hx197 : Bounds (36395811 / 39062500) (932279826639 / 1000000000000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx196 <;> norm_num
  let x198 : ℝ := (1 / 1)-x195
  have hx198 : Bounds (36395811 / 39062500) (932279826639 / 1000000000000) x198 := by
    exact hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (1260231 / 1000000) (7883 / 6250) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-1633 / 6250) (-260231 / 1000000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (4617 / 6250) (739769 / 1000000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (4617 / 6250) (739769 / 1000000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (675886661917 / 500000000000) (1353692874161 / 1000000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (425886661917 / 250000000000) (853692874161 / 500000000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (425886661917 / 250000000000) (853692874161 / 500000000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (532712341 / 1000000000) (534963399 / 1000000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_12522.1) (by simpa only [div_one] using reflection_log_12523.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (532712341 / 2000000000) (534963399 / 2000000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (532712341 / 2000000000) (534963399 / 2000000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (1 / 1)+a
  have hx210 : Bounds (1497 / 1000) (749 / 500) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) ha <;> norm_num
  let x211 : ℝ := -a
  have hx211 : Bounds (-249 / 500) (-497 / 1000) x211 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg ha
  let x212 : ℝ := (1 / 1)+x211
  have hx212 : Bounds (251 / 500) (503 / 1000) x212 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx211 <;> norm_num
  let x213 : ℝ := (1 / 1)-a
  have hx213 : Bounds (251 / 500) (503 / 1000) x213 := by
    exact hx212
  let x214 : ℝ := x213⁻¹
  have hx214 : Bounds (124254473161 / 62500000000) (199203187251 / 100000000000) x214 := by
    apply bounds_inv hx213 <;> norm_num
  let x215 : ℝ := x210*x214
  have hx215 : Bounds (93004473161 / 31250000000) (149203187251 / 50000000000) x215 := by
    apply bounds_mul hx210 hx214 <;> norm_num
  let x216 : ℝ := x210/x213
  have hx216 : Bounds (93004473161 / 31250000000) (149203187251 / 50000000000) x216 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx215
  let x217 : ℝ := Real.log x216
  have hx217 : Bounds (1090628213 / 1000000000) (218657209 / 200000000) x217 := by
    exact bounds_log hx216 (by norm_num) (by simpa only [div_one] using reflection_log_12524.1) (by simpa only [div_one] using reflection_log_12525.2)
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (1090628213 / 2000000000) (218657209 / 400000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (1090628213 / 2000000000) (218657209 / 400000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := (2 / 1)*x192
  have hx221 : Bounds (728208313 / 500000000) (364250901 / 250000000) x221 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x222 : ℝ := c*(1 / 1)
  have hx222 : Bounds (260231 / 1000000) (1633 / 6250) x222 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x223 : ℝ := c*x222
  have hx223 : Bounds (67720173361 / 1000000000000) (2666689 / 39062500) x223 := by
    apply bounds_mul hc hx222 <;> norm_num
  let x224 : ℝ := c^2
  have hx224 : Bounds (67720173361 / 1000000000000) (2666689 / 39062500) x224 := by
    (convert hx223 using 1; ring)
  let x225 : ℝ := -x224
  have hx225 : Bounds (-2666689 / 39062500) (-67720173361 / 1000000000000) x225 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx224
  let x226 : ℝ := x221+x225
  have hx226 : Bounds (3470373469 / 2500000000) (1389283430639 / 1000000000000) x226 := by
    apply bounds_add hx221 hx225 <;> norm_num
  let x227 : ℝ := x221-x224
  have hx227 : Bounds (3470373469 / 2500000000) (1389283430639 / 1000000000000) x227 := by
    exact hx226
  let x228 : ℝ := x180*x227
  have hx228 : Bounds (457127436741 / 500000000000) (228847692363 / 250000000000) x228 := by
    apply bounds_mul hx180 hx227 <;> norm_num
  let x229 : ℝ := (2 / 1)*x90
  have hx229 : Bounds (125657814679 / 100000000000) (628562126411 / 500000000000) x229 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x230 : ℝ := x198*(1 / 1)
  have hx230 : Bounds (36395811 / 39062500) (932279826639 / 1000000000000) x230 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x231 : ℝ := x198*x230
  have hx231 : Bounds (434062969519 / 500000000000) (869145675159 / 1000000000000) x231 := by
    apply bounds_mul hx198 hx230 <;> norm_num
  let x232 : ℝ := x198^2
  have hx232 : Bounds (434062969519 / 500000000000) (869145675159 / 1000000000000) x232 := by
    (convert hx231 using 1; ring)
  let x233 : ℝ := x229*x232
  have hx233 : Bounds (136358510457 / 125000000000) (546312053739 / 500000000000) x233 := by
    apply bounds_mul hx229 hx232 <;> norm_num
  let x234 : ℝ := x192*(1 / 1)
  have hx234 : Bounds (728208313 / 1000000000) (364250901 / 500000000) x234 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x235 : ℝ := x192*x234
  have hx235 : Bounds (265143673561 / 500000000000) (265357437759 / 500000000000) x235 := by
    apply bounds_mul hx192 hx234 <;> norm_num
  let x236 : ℝ := x192*x235
  have hx236 : Bounds (96539913613 / 250000000000) (96656685791 / 250000000000) x236 := by
    apply bounds_mul hx192 hx235 <;> norm_num
  let x237 : ℝ := x192^3
  have hx237 : Bounds (96539913613 / 250000000000) (96656685791 / 250000000000) x237 := by
    (convert hx236 using 1; ring)
  let x238 : ℝ := x233*x237
  have hx238 : Bounds (421249242237 / 1000000000000) (422437700177 / 1000000000000) x238 := by
    apply bounds_mul hx233 hx237 <;> norm_num
  let x239 : ℝ := x238⁻¹
  have hx239 : Bounds (2367212963191 / 1000000000000) (2373891510617 / 1000000000000) x239 := by
    apply bounds_inv hx238 <;> norm_num
  let x240 : ℝ := x228*x239
  have hx240 : Bounds (2164235988167 / 1000000000000) (4346076753 / 2000000000) x240 := by
    apply bounds_mul hx228 hx239 <;> norm_num
  let x241 : ℝ := x228/x238
  have hx241 : Bounds (2164235988167 / 1000000000000) (4346076753 / 2000000000) x241 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx240
  let x242 : ℝ := -x209
  have hx242 : Bounds (-534963399 / 2000000000) (-532712341 / 2000000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x243 : ℝ := (2 / 1)*x192
  have hx243 : Bounds (728208313 / 500000000) (364250901 / 250000000) x243 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x244 : ℝ := c*(1 / 1)
  have hx244 : Bounds (260231 / 1000000) (1633 / 6250) x244 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x245 : ℝ := c*x244
  have hx245 : Bounds (67720173361 / 1000000000000) (2666689 / 39062500) x245 := by
    apply bounds_mul hc hx244 <;> norm_num
  let x246 : ℝ := c^2
  have hx246 : Bounds (67720173361 / 1000000000000) (2666689 / 39062500) x246 := by
    (convert hx245 using 1; ring)
  let x247 : ℝ := -x246
  have hx247 : Bounds (-2666689 / 39062500) (-67720173361 / 1000000000000) x247 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx246
  let x248 : ℝ := x243+x247
  have hx248 : Bounds (3470373469 / 2500000000) (1389283430639 / 1000000000000) x248 := by
    apply bounds_add hx243 hx247 <;> norm_num
  let x249 : ℝ := x243-x246
  have hx249 : Bounds (3470373469 / 2500000000) (1389283430639 / 1000000000000) x249 := by
    exact hx248
  let x250 : ℝ := x242*x249
  have hx250 : Bounds (-74321578623 / 200000000000) (-369742154963 / 1000000000000) x250 := by
    apply bounds_mul hx242 hx249 <;> norm_num
  let x251 : ℝ := x198⁻¹
  have hx251 : Bounds (214527864151 / 200000000000) (1073269118801 / 1000000000000) x251 := by
    apply bounds_inv hx198 <;> norm_num
  let x252 : ℝ := c*x251
  have hx252 : Bounds (279134003079 / 1000000000000) (280423755361 / 1000000000000) x252 := by
    apply bounds_mul hc hx251 <;> norm_num
  let x253 : ℝ := c/x198
  have hx253 : Bounds (279134003079 / 1000000000000) (280423755361 / 1000000000000) x253 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx252
  let x254 : ℝ := (2 / 1)*x253
  have hx254 : Bounds (279134003079 / 500000000000) (280423755361 / 500000000000) x254 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx253 <;> norm_num
  let x255 : ℝ := (2 / 1)*c
  have hx255 : Bounds (260231 / 500000) (1633 / 3125) x255 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hc <;> norm_num
  let x256 : ℝ := -x255
  have hx256 : Bounds (-1633 / 3125) (-260231 / 500000) x256 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx255
  let x257 : ℝ := x254+x256
  have hx257 : Bounds (17854003079 / 500000000000) (20192755361 / 500000000000) x257 := by
    apply bounds_add hx254 hx256 <;> norm_num
  let x258 : ℝ := x254-x255
  have hx258 : Bounds (17854003079 / 500000000000) (20192755361 / 500000000000) x258 := by
    exact hx257
  let x259 : ℝ := x180*x258
  have hx259 : Bounds (5879449817 / 250000000000) (207888891 / 7812500000) x259 := by
    apply bounds_mul hx180 hx258 <;> norm_num
  let x260 : ℝ := x250+x259
  have hx260 : Bounds (-348090093847 / 1000000000000) (-68626475383 / 200000000000) x260 := by
    apply bounds_add hx250 hx259 <;> norm_num
  let x261 : ℝ := (2 / 1)*x90
  have hx261 : Bounds (125657814679 / 100000000000) (628562126411 / 500000000000) x261 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x262 : ℝ := x198*(1 / 1)
  have hx262 : Bounds (36395811 / 39062500) (932279826639 / 1000000000000) x262 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x263 : ℝ := x198*x262
  have hx263 : Bounds (434062969519 / 500000000000) (869145675159 / 1000000000000) x263 := by
    apply bounds_mul hx198 hx262 <;> norm_num
  let x264 : ℝ := x198^2
  have hx264 : Bounds (434062969519 / 500000000000) (869145675159 / 1000000000000) x264 := by
    (convert hx263 using 1; ring)
  let x265 : ℝ := x261*x264
  have hx265 : Bounds (136358510457 / 125000000000) (546312053739 / 500000000000) x265 := by
    apply bounds_mul hx261 hx264 <;> norm_num
  let x266 : ℝ := x192*(1 / 1)
  have hx266 : Bounds (728208313 / 1000000000) (364250901 / 500000000) x266 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x267 : ℝ := x192*x266
  have hx267 : Bounds (265143673561 / 500000000000) (265357437759 / 500000000000) x267 := by
    apply bounds_mul hx192 hx266 <;> norm_num
  let x268 : ℝ := x192*x267
  have hx268 : Bounds (96539913613 / 250000000000) (96656685791 / 250000000000) x268 := by
    apply bounds_mul hx192 hx267 <;> norm_num
  let x269 : ℝ := x192^3
  have hx269 : Bounds (96539913613 / 250000000000) (96656685791 / 250000000000) x269 := by
    (convert hx268 using 1; ring)
  let x270 : ℝ := x265*x269
  have hx270 : Bounds (421249242237 / 1000000000000) (422437700177 / 1000000000000) x270 := by
    apply bounds_mul hx265 hx269 <;> norm_num
  let x271 : ℝ := x270⁻¹
  have hx271 : Bounds (2367212963191 / 1000000000000) (2373891510617 / 1000000000000) x271 := by
    apply bounds_inv hx270 <;> norm_num
  let x272 : ℝ := x260*x271
  have hx272 : Bounds (-413164059357 / 500000000000) (-812267410723 / 1000000000000) x272 := by
    apply bounds_mul hx260 hx271 <;> norm_num
  let x273 : ℝ := x260/x270
  have hx273 : Bounds (-413164059357 / 500000000000) (-812267410723 / 1000000000000) x273 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx272
  let x274 : ℝ := (4 / 1)*c
  have hx274 : Bounds (260231 / 250000) (3266 / 3125) x274 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hc <;> norm_num
  let x275 : ℝ := x198⁻¹
  have hx275 : Bounds (214527864151 / 200000000000) (1073269118801 / 1000000000000) x275 := by
    apply bounds_inv hx198 <;> norm_num
  let x276 : ℝ := x274*x275
  have hx276 : Bounds (1116536012317 / 1000000000000) (560847510721 / 500000000000) x276 := by
    apply bounds_mul hx274 hx275 <;> norm_num
  let x277 : ℝ := x274/x198
  have hx277 : Bounds (1116536012317 / 1000000000000) (560847510721 / 500000000000) x277 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx276
  let x278 : ℝ := (3 / 1)*c
  have hx278 : Bounds (780693 / 1000000) (4899 / 6250) x278 := by
    apply bounds_mul (bounds_const ((3 / 1) : ℝ)) hc <;> norm_num
  let x279 : ℝ := x198*x192
  have hx279 : Bounds (678495542491 / 1000000000000) (27166701347 / 40000000000) x279 := by
    apply bounds_mul hx198 hx192 <;> norm_num
  let x280 : ℝ := x279⁻¹
  have hx280 : Bounds (1472390758417 / 1000000000000) (1473849034187 / 1000000000000) x280 := by
    apply bounds_inv hx279 <;> norm_num
  let x281 : ℝ := x278*x280
  have hx281 : Bounds (28737128959 / 25000000000) (577630913479 / 500000000000) x281 := by
    apply bounds_mul hx278 hx280 <;> norm_num
  let x282 : ℝ := x278/x279
  have hx282 : Bounds (28737128959 / 25000000000) (577630913479 / 500000000000) x282 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx281
  let x283 : ℝ := -x282
  have hx283 : Bounds (-577630913479 / 500000000000) (-28737128959 / 25000000000) x283 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx282
  let x284 : ℝ := x277+x283
  have hx284 : Bounds (-38725814641 / 1000000000000) (-13895068459 / 500000000000) x284 := by
    apply bounds_add hx277 hx283 <;> norm_num
  let x285 : ℝ := x277-x282
  have hx285 : Bounds (-38725814641 / 1000000000000) (-13895068459 / 500000000000) x285 := by
    exact hx284
  let x286 : ℝ := x241*x285
  have hx286 : Bounds (-84152681377 / 1000000000000) (-30072207217 / 500000000000) x286 := by
    apply bounds_mul hx241 hx285 <;> norm_num
  let x287 : ℝ := x273+x286
  have hx287 : Bounds (-910480800091 / 1000000000000) (-872411825157 / 1000000000000) x287 := by
    apply bounds_add hx273 hx286 <;> norm_num
  let x288 : ℝ := (2 / 1)*x192
  have hx288 : Bounds (728208313 / 500000000) (364250901 / 250000000) x288 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x289 : ℝ := c*(1 / 1)
  have hx289 : Bounds (260231 / 1000000) (1633 / 6250) x289 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x290 : ℝ := c*x289
  have hx290 : Bounds (67720173361 / 1000000000000) (2666689 / 39062500) x290 := by
    apply bounds_mul hc hx289 <;> norm_num
  let x291 : ℝ := c^2
  have hx291 : Bounds (67720173361 / 1000000000000) (2666689 / 39062500) x291 := by
    (convert hx290 using 1; ring)
  let x292 : ℝ := -x291
  have hx292 : Bounds (-2666689 / 39062500) (-67720173361 / 1000000000000) x292 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx291
  let x293 : ℝ := x288+x292
  have hx293 : Bounds (3470373469 / 2500000000) (1389283430639 / 1000000000000) x293 := by
    apply bounds_add hx288 hx292 <;> norm_num
  let x294 : ℝ := x288-x291
  have hx294 : Bounds (3470373469 / 2500000000) (1389283430639 / 1000000000000) x294 := by
    exact hx293
  let x295 : ℝ := c*x294
  have hx295 : Bounds (90309875821 / 250000000000) (181495987379 / 500000000000) x295 := by
    apply bounds_mul hc hx294 <;> norm_num
  let x296 : ℝ := x198*(1 / 1)
  have hx296 : Bounds (36395811 / 39062500) (932279826639 / 1000000000000) x296 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x297 : ℝ := x198*x296
  have hx297 : Bounds (434062969519 / 500000000000) (869145675159 / 1000000000000) x297 := by
    apply bounds_mul hx198 hx296 <;> norm_num
  let x298 : ℝ := x198^2
  have hx298 : Bounds (434062969519 / 500000000000) (869145675159 / 1000000000000) x298 := by
    (convert hx297 using 1; ring)
  let x299 : ℝ := x192*(1 / 1)
  have hx299 : Bounds (728208313 / 1000000000) (364250901 / 500000000) x299 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x300 : ℝ := x192*x299
  have hx300 : Bounds (265143673561 / 500000000000) (265357437759 / 500000000000) x300 := by
    apply bounds_mul hx192 hx299 <;> norm_num
  let x301 : ℝ := x192^2
  have hx301 : Bounds (265143673561 / 500000000000) (265357437759 / 500000000000) x301 := by
    (convert hx300 using 1; ring)
  let x302 : ℝ := x298*x301
  have hx302 : Bounds (23017810059 / 50000000000) (1153171347 / 2500000000) x302 := by
    apply bounds_mul hx298 hx301 <;> norm_num
  let x303 : ℝ := x302⁻¹
  have hx303 : Bounds (2167934545463 / 1000000000000) (2172230975573 / 1000000000000) x303 := by
    apply bounds_inv hx302 <;> norm_num
  let x304 : ℝ := x295*x303
  have hx304 : Bounds (156628719671 / 200000000000) (394251205727 / 500000000000) x304 := by
    apply bounds_mul hx295 hx303 <;> norm_num
  let x305 : ℝ := x295/x302
  have hx305 : Bounds (156628719671 / 200000000000) (394251205727 / 500000000000) x305 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx304
  let x306 : ℝ := c*x220
  have hx306 : Bounds (8869227203 / 62500000000) (142826888919 / 1000000000000) x306 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x307 : ℝ := x180+x306
  have hx307 : Bounds (400260908651 / 500000000000) (400860535407 / 500000000000) x307 := by
    apply bounds_add hx180 hx306 <;> norm_num
  let x308 : ℝ := x307*(1 / 1)
  have hx308 : Bounds (400260908651 / 500000000000) (400860535407 / 500000000000) x308 := by
    apply bounds_mul hx307 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x309 : ℝ := x307*x308
  have hx309 : Bounds (80104397497 / 125000000000) (160689168847 / 250000000000) x309 := by
    apply bounds_mul hx307 hx308 <;> norm_num
  let x310 : ℝ := x307^2
  have hx310 : Bounds (80104397497 / 125000000000) (160689168847 / 250000000000) x310 := by
    (convert hx309 using 1; ring)
  let x311 : ℝ := x287*x310
  have hx311 : Bounds (-73152201509 / 125000000000) (-559072188987 / 1000000000000) x311 := by
    apply bounds_mul hx287 hx310 <;> norm_num
  let x312 : ℝ := (2 / 1)*x241
  have hx312 : Bounds (2164235988167 / 500000000000) (4346076753 / 1000000000) x312 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx241 <;> norm_num
  let x313 : ℝ := c*x220
  have hx313 : Bounds (8869227203 / 62500000000) (142826888919 / 1000000000000) x313 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x314 : ℝ := x180+x313
  have hx314 : Bounds (400260908651 / 500000000000) (400860535407 / 500000000000) x314 := by
    apply bounds_add hx180 hx313 <;> norm_num
  let x315 : ℝ := x312*x314
  have hx315 : Bounds (693007250527 / 200000000000) (696868261651 / 200000000000) x315 := by
    apply bounds_mul hx312 hx314 <;> norm_num
  let x316 : ℝ := -x209
  have hx316 : Bounds (-534963399 / 2000000000) (-532712341 / 2000000000) x316 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x317 : ℝ := x220+x316
  have hx317 : Bounds (277832407 / 1000000000) (70071713 / 250000000) x317 := by
    apply bounds_add hx220 hx316 <;> norm_num
  let x318 : ℝ := x220-x209
  have hx318 : Bounds (277832407 / 1000000000) (70071713 / 250000000) x318 := by
    exact hx317
  let x319 : ℝ := x315*x318
  have hx319 : Bounds (962699362411 / 1000000000000) (195323011317 / 200000000000) x319 := by
    apply bounds_mul hx315 hx318 <;> norm_num
  let x320 : ℝ := x311+x319
  have hx320 : Bounds (377481750339 / 1000000000000) (208771433799 / 500000000000) x320 := by
    apply bounds_add hx311 hx319 <;> norm_num
  let x321 : ℝ := a*(1 / 1)
  have hx321 : Bounds (497 / 1000) (249 / 500) x321 := by
    apply bounds_mul ha (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x322 : ℝ := a*x321
  have hx322 : Bounds (247009 / 1000000) (62001 / 250000) x322 := by
    apply bounds_mul ha hx321 <;> norm_num
  let x323 : ℝ := a^2
  have hx323 : Bounds (247009 / 1000000) (62001 / 250000) x323 := by
    (convert hx322 using 1; ring)
  let x324 : ℝ := -x323
  have hx324 : Bounds (-62001 / 250000) (-247009 / 1000000) x324 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx323
  let x325 : ℝ := (1 / 1)+x324
  have hx325 : Bounds (187999 / 250000) (752991 / 1000000) x325 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx324 <;> norm_num
  let x326 : ℝ := (1 / 1)-x323
  have hx326 : Bounds (187999 / 250000) (752991 / 1000000) x326 := by
    exact hx325
  let x327 : ℝ := x326⁻¹
  have hx327 : Bounds (1328037121293 / 1000000000000) (1329794307417 / 1000000000000) x327 := by
    apply bounds_inv hx326 <;> norm_num
  let x328 : ℝ := (1 / 1)*x327
  have hx328 : Bounds (1328037121293 / 1000000000000) (1329794307417 / 1000000000000) x328 := by
    apply bounds_mul (bounds_const ((1 / 1) : ℝ)) hx327 <;> norm_num
  let x329 : ℝ := (1 / 1)/x326
  have hx329 : Bounds (1328037121293 / 1000000000000) (1329794307417 / 1000000000000) x329 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx328
  let x330 : ℝ := x329*x305
  have hx330 : Bounds (520021884959 / 500000000000) (1048546018137 / 1000000000000) x330 := by
    apply bounds_mul hx329 hx305 <;> norm_num
  let x331 : ℝ := x320+x330
  have hx331 : Bounds (1417525520257 / 1000000000000) (293217777147 / 200000000000) x331 := by
    apply bounds_add hx320 hx330 <;> norm_num
  let x332 : ℝ := x180*(1 / 1)
  have hx332 : Bounds (329307091027 / 500000000000) (131778836379 / 200000000000) x332 := by
    apply bounds_mul hx180 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x333 : ℝ := x180*x332
  have hx333 : Bounds (216886320401 / 500000000000) (54267692867 / 125000000000) x333 := by
    apply bounds_mul hx180 hx332 <;> norm_num
  let x334 : ℝ := x180^2
  have hx334 : Bounds (216886320401 / 500000000000) (54267692867 / 125000000000) x334 := by
    (convert hx333 using 1; ring)
  let x335 : ℝ := x331*x334
  have hx335 : Bounds (307441894163 / 500000000000) (127298018187 / 200000000000) x335 := by
    apply bounds_mul hx331 hx334 <;> norm_num
  let x336 : ℝ := x90*x192
  have hx336 : Bounds (457525326213 / 1000000000000) (2861929011 / 6250000000) x336 := by
    apply bounds_mul hx90 hx192 <;> norm_num
  let x337 : ℝ := x336⁻¹
  have hx337 : Bounds (2183841729119 / 1000000000000) (546417838919 / 250000000000) x337 := by
    apply bounds_inv hx336 <;> norm_num
  let x338 : ℝ := x335*x337
  have hx338 : Bounds (268561775101 / 200000000000) (1391158159929 / 1000000000000) x338 := by
    apply bounds_mul hx335 hx337 <;> norm_num
  let x339 : ℝ := x335/x336
  have hx339 : Bounds (268561775101 / 200000000000) (1391158159929 / 1000000000000) x339 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx338
  have hu : x339 < (1782780341458166494288249 / 1133990892162000000000000) := lt_of_le_of_lt hx339.2 (by norm_num)
  simpa +zetaDelta only [ScFormula,Kprime,K,Mprime,SmallMean.A,biasB,div_one,pow_two] using hu

open GeneralCK.Reflection
/-- Uniform derivative enclosure including input boxes with z=0. -/
theorem derivative_bound_897 {a z s : ℝ}
    (ha : a ∈ Set.Icc ((497 / 1000):ℝ) ((249 / 500)))
    (hz : z ∈ Set.Icc (0:ℝ) (1/1000))
    (hs : s ∈ Set.Ioo (a*(1-z)/2) (a*(1+z)/2)) :
    P a ((biasE a+biasE (a*z))/2) s ≤ (1782780341458166494288249 / 1133990892162000000000000) := by
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
  have hsl : (496503 / 2000000) ≤ s := by
    have h := mul_le_mul ha.1 (show (999/1000:ℝ) ≤ 1-z by linarith [hz.2])
      (by norm_num : (0:ℝ) ≤ 999/1000) ha0.le
    nlinarith [hs.1]
  have hsu : s ≤ (249249 / 1000000) := by
    have h := mul_le_mul ha.2 (show 1+z ≤ (1001/1000:ℝ) by linarith [hz.2])
      (by linarith [hz.1] : 0 ≤ 1+z) (by norm_num : (0:ℝ) ≤ (249 / 500))
    nlinarith [hs.2]
  have hy := div_pos he hs0
  have hc := biasContact_mem hy
  have heq : biasE (biasContact (((biasE a+biasE (a*z))/2)/s)) =
      (((biasE a+biasE (a*z))/2)/s)*biasContact (((biasE a+biasE (a*z))/2)/s) := by
    exact (div_eq_iff hc.1.ne').mp (biasR_biasContact hy)
  have hb := derivative_leaf_897 a z s _ ha hz ⟨hsl,hsu⟩ hc.1.le hc.2.le heq
  rw [P_eq_formula ha0 ha1 he hs0]
  exact hb.le

/-- Checked low-ratio strip: includes arbitrarily small positive z. -/
theorem curvature_leaf_897 {a z : ℝ}
    (ha : a ∈ Set.Icc ((497 / 1000):ℝ) ((249 / 500)))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < curvature a (a*z) := by
  have ha0 : 0 < a := by linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  apply curvature_pos_of_derivative_bound ha0 ha1 hz.1 (by linarith [hz.2])
    (fun s hs => derivative_bound_897 ha ⟨hz.1.le,hz.2⟩ hs) (M := (1782780341458166494288249 / 1133990892162000000000000))
  exact lt_of_lt_of_le (by norm_num : (1782780341458166494288249 / 1133990892162000000000000) < 2*((497 / 1000):ℝ)/(1-((497 / 1000):ℝ)^2)^2)
    (base_mono (by norm_num) ha.1 ha1)

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Cell0898 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
theorem derivative_leaf_898 (a z s c : ℝ)
    (ha : Bounds (249 / 500) (499 / 1000) a) (hz : Bounds 0 (1/1000) z)
    (hs : Bounds (248751 / 1000000) (499499 / 2000000) s) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (heq : biasE c = (((biasE a+biasE (a*z))/2)/s)*c) :
    ScFormula c a ((biasE a+biasE (a*z))/2)*(biasE c)^2 /
      (((biasE a+biasE (a*z))/2)*biasB c) < (111591437014759247003793 / 70687248002000000000000) := by
  let x0 : ℝ := Real.log (2 / 1)
  have hx0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x0 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x1 : ℝ := (1 / 1)+(499 / 1000)
  have hx1 : Bounds (1499 / 1000) (1499 / 1000) x1 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((499 / 1000) : ℝ)) <;> norm_num
  let x2 : ℝ := (1 / 1)+(499 / 1000)
  have hx2 : Bounds (1499 / 1000) (1499 / 1000) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((499 / 1000) : ℝ)) <;> norm_num
  let x3 : ℝ := Real.log x2
  have hx3 : Bounds (404798219 / 1000000000) (20239911 / 50000000) x3 := by
    exact bounds_log hx2 (by norm_num) (by simpa only [div_one] using reflection_log_12526.1) (by simpa only [div_one] using reflection_log_12526.2)
  let x4 : ℝ := x1*x3
  have hx4 : Bounds (606792530281 / 1000000000000) (30339626589 / 50000000000) x4 := by
    apply bounds_mul hx1 hx3 <;> norm_num
  let x5 : ℝ := -(499 / 1000)
  have hx5 : Bounds (-499 / 1000) (-499 / 1000) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((499 / 1000) : ℝ))
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (501 / 1000) (501 / 1000) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-(499 / 1000)
  have hx7 : Bounds (501 / 1000) (501 / 1000) x7 := by
    exact hx6
  let x8 : ℝ := -(499 / 1000)
  have hx8 : Bounds (-499 / 1000) (-499 / 1000) x8 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((499 / 1000) : ℝ))
  let x9 : ℝ := (1 / 1)+x8
  have hx9 : Bounds (501 / 1000) (501 / 1000) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx8 <;> norm_num
  let x10 : ℝ := (1 / 1)-(499 / 1000)
  have hx10 : Bounds (501 / 1000) (501 / 1000) x10 := by
    exact hx9
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (-345574589 / 500000000) (-691149177 / 1000000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_12527.1) (by simpa only [div_one] using reflection_log_12527.2)
  let x12 : ℝ := x7*x11
  have hx12 : Bounds (-173132869089 / 500000000000) (-346265737677 / 1000000000000) x12 := by
    apply bounds_mul hx7 hx11 <;> norm_num
  let x13 : ℝ := x4+x12
  have hx13 : Bounds (260526792103 / 1000000000000) (260526794103 / 1000000000000) x13 := by
    apply bounds_add hx4 hx12 <;> norm_num
  let x14 : ℝ := (2 / 1)⁻¹
  have hx14 : Bounds (1 / 2) (1 / 2) x14 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x15 : ℝ := x13*x14
  have hx15 : Bounds (130263396051 / 1000000000000) (32565849263 / 250000000000) x15 := by
    apply bounds_mul hx13 hx14 <;> norm_num
  let x16 : ℝ := x13/(2 / 1)
  have hx16 : Bounds (130263396051 / 1000000000000) (32565849263 / 250000000000) x16 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx15
  let x17 : ℝ := -x16
  have hx17 : Bounds (-32565849263 / 250000000000) (-130263396051 / 1000000000000) x17 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx16
  let x18 : ℝ := x0+x17
  have hx18 : Bounds (140720945737 / 250000000000) (562883784949 / 1000000000000) x18 := by
    apply bounds_add hx0 hx17 <;> norm_num
  let x19 : ℝ := x0-x16
  have hx19 : Bounds (140720945737 / 250000000000) (562883784949 / 1000000000000) x19 := by
    exact hx18
  let x20 : ℝ := biasE (499 / 1000)
  have hx20 : Bounds (140720945737 / 250000000000) (562883784949 / 1000000000000) x20 := by
    simpa +zetaDelta only [biasE, div_one] using hx19
  let x21 : ℝ := Real.log (2 / 1)
  have hx21 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x21 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x22 : ℝ := (1 / 1)+(249 / 500)
  have hx22 : Bounds (749 / 500) (749 / 500) x22 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((249 / 500) : ℝ)) <;> norm_num
  let x23 : ℝ := (1 / 1)+(249 / 500)
  have hx23 : Bounds (749 / 500) (749 / 500) x23 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((249 / 500) : ℝ)) <;> norm_num
  let x24 : ℝ := Real.log x23
  have hx24 : Bounds (80826177 / 200000000) (202065443 / 500000000) x24 := by
    exact bounds_log hx23 (by norm_num) (by simpa only [div_one] using reflection_log_12512.1) (by simpa only [div_one] using reflection_log_12512.2)
  let x25 : ℝ := x22*x24
  have hx25 : Bounds (60538806573 / 100000000000) (151347016807 / 250000000000) x25 := by
    apply bounds_mul hx22 hx24 <;> norm_num
  let x26 : ℝ := -(249 / 500)
  have hx26 : Bounds (-249 / 500) (-249 / 500) x26 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((249 / 500) : ℝ))
  let x27 : ℝ := (1 / 1)+x26
  have hx27 : Bounds (251 / 500) (251 / 500) x27 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx26 <;> norm_num
  let x28 : ℝ := (1 / 1)-(249 / 500)
  have hx28 : Bounds (251 / 500) (251 / 500) x28 := by
    exact hx27
  let x29 : ℝ := -(249 / 500)
  have hx29 : Bounds (-249 / 500) (-249 / 500) x29 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((249 / 500) : ℝ))
  let x30 : ℝ := (1 / 1)+x29
  have hx30 : Bounds (251 / 500) (251 / 500) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx29 <;> norm_num
  let x31 : ℝ := (1 / 1)-(249 / 500)
  have hx31 : Bounds (251 / 500) (251 / 500) x31 := by
    exact hx30
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (-17228879 / 25000000) (-689155159 / 1000000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_12513.1) (by simpa only [div_one] using reflection_log_12513.2)
  let x33 : ℝ := x28*x32
  have hx33 : Bounds (-4324448629 / 12500000000) (-172977944909 / 500000000000) x33 := by
    apply bounds_mul hx28 hx32 <;> norm_num
  let x34 : ℝ := x25+x33
  have hx34 : Bounds (25943217541 / 100000000000) (25943217741 / 100000000000) x34 := by
    apply bounds_add hx25 hx33 <;> norm_num
  let x35 : ℝ := (2 / 1)⁻¹
  have hx35 : Bounds (1 / 2) (1 / 2) x35 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x36 : ℝ := x34*x35
  have hx36 : Bounds (25943217541 / 200000000000) (25943217741 / 200000000000) x36 := by
    apply bounds_mul hx34 hx35 <;> norm_num
  let x37 : ℝ := x34/(2 / 1)
  have hx37 : Bounds (25943217541 / 200000000000) (25943217741 / 200000000000) x37 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx36
  let x38 : ℝ := -x37
  have hx38 : Bounds (-25943217741 / 200000000000) (-25943217541 / 200000000000) x38 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx37
  let x39 : ℝ := x21+x38
  have hx39 : Bounds (112686218259 / 200000000000) (112686218659 / 200000000000) x39 := by
    apply bounds_add hx21 hx38 <;> norm_num
  let x40 : ℝ := x21-x37
  have hx40 : Bounds (112686218259 / 200000000000) (112686218659 / 200000000000) x40 := by
    exact hx39
  let x41 : ℝ := biasE (249 / 500)
  have hx41 : Bounds (112686218259 / 200000000000) (112686218659 / 200000000000) x41 := by
    simpa +zetaDelta only [biasE, div_one] using hx40
  let x42 : ℝ := biasE a
  have hx42 : Bounds (140720945737 / 250000000000) (112686218659 / 200000000000) x42 := by
    exact bounds_biasE ha (by norm_num) (by norm_num) hx20.1 hx41.2
  let x43 : ℝ := a*z
  have hx43 : Bounds (0 / 1) (499 / 1000000) x43 := by
    apply bounds_mul ha hz <;> norm_num
  let x44 : ℝ := Real.log (2 / 1)
  have hx44 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x44 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x45 : ℝ := (1 / 1)+(499 / 1000000)
  have hx45 : Bounds (1000499 / 1000000) (1000499 / 1000000) x45 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((499 / 1000000) : ℝ)) <;> norm_num
  let x46 : ℝ := (1 / 1)+(499 / 1000000)
  have hx46 : Bounds (1000499 / 1000000) (1000499 / 1000000) x46 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((499 / 1000000) : ℝ)) <;> norm_num
  let x47 : ℝ := Real.log x46
  have hx47 : Bounds (3991 / 8000000) (124719 / 250000000) x47 := by
    exact bounds_log hx46 (by norm_num) (by simpa only [div_one] using reflection_log_12528.1) (by simpa only [div_one] using reflection_log_12528.2)
  let x48 : ℝ := x45*x47
  have hx48 : Bounds (249561969 / 500000000000) (24956247 / 50000000000) x48 := by
    apply bounds_mul hx45 hx47 <;> norm_num
  let x49 : ℝ := -(499 / 1000000)
  have hx49 : Bounds (-499 / 1000000) (-499 / 1000000) x49 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((499 / 1000000) : ℝ))
  let x50 : ℝ := (1 / 1)+x49
  have hx50 : Bounds (999501 / 1000000) (999501 / 1000000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx49 <;> norm_num
  let x51 : ℝ := (1 / 1)-(499 / 1000000)
  have hx51 : Bounds (999501 / 1000000) (999501 / 1000000) x51 := by
    exact hx50
  let x52 : ℝ := -(499 / 1000000)
  have hx52 : Bounds (-499 / 1000000) (-499 / 1000000) x52 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((499 / 1000000) : ℝ))
  let x53 : ℝ := (1 / 1)+x52
  have hx53 : Bounds (999501 / 1000000) (999501 / 1000000) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx52 <;> norm_num
  let x54 : ℝ := (1 / 1)-(499 / 1000000)
  have hx54 : Bounds (999501 / 1000000) (999501 / 1000000) x54 := by
    exact hx53
  let x55 : ℝ := Real.log x54
  have hx55 : Bounds (-3993 / 8000000) (-124781 / 250000000) x55 := by
    exact bounds_log hx54 (by norm_num) (by simpa only [div_one] using reflection_log_12529.1) (by simpa only [div_one] using reflection_log_12529.2)
  let x56 : ℝ := x51*x55
  have hx56 : Bounds (-498875937 / 1000000000000) (-498874937 / 1000000000000) x56 := by
    apply bounds_mul hx51 hx55 <;> norm_num
  let x57 : ℝ := x48+x56
  have hx57 : Bounds (248001 / 1000000000000) (250003 / 1000000000000) x57 := by
    apply bounds_add hx48 hx56 <;> norm_num
  let x58 : ℝ := (2 / 1)⁻¹
  have hx58 : Bounds (1 / 2) (1 / 2) x58 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x59 : ℝ := x57*x58
  have hx59 : Bounds (31 / 250000000) (62501 / 500000000000) x59 := by
    apply bounds_mul hx57 hx58 <;> norm_num
  let x60 : ℝ := x57/(2 / 1)
  have hx60 : Bounds (31 / 250000000) (62501 / 500000000000) x60 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx59
  let x61 : ℝ := -x60
  have hx61 : Bounds (-62501 / 500000000000) (-31 / 250000000) x61 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx60
  let x62 : ℝ := x44+x61
  have hx62 : Bounds (346573527499 / 500000000000) (693147057 / 1000000000) x62 := by
    apply bounds_add hx44 hx61 <;> norm_num
  let x63 : ℝ := x44-x60
  have hx63 : Bounds (346573527499 / 500000000000) (693147057 / 1000000000) x63 := by
    exact hx62
  let x64 : ℝ := biasE (499 / 1000000)
  have hx64 : Bounds (346573527499 / 500000000000) (693147057 / 1000000000) x64 := by
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
  have hx86 : Bounds (346573527499 / 500000000000) (693147181 / 1000000000) x86 := by
    exact bounds_biasE hx43 (by norm_num) (by norm_num) hx64.1 hx85.2
  let x87 : ℝ := x42+x86
  have hx87 : Bounds (628015418973 / 500000000000) (251315654859 / 200000000000) x87 := by
    apply bounds_add hx42 hx86 <;> norm_num
  let x88 : ℝ := (2 / 1)⁻¹
  have hx88 : Bounds (1 / 2) (1 / 2) x88 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x89 : ℝ := x87*x88
  have hx89 : Bounds (628015418973 / 1000000000000) (157072284287 / 250000000000) x89 := by
    apply bounds_mul hx87 hx88 <;> norm_num
  let x90 : ℝ := x87/(2 / 1)
  have hx90 : Bounds (628015418973 / 1000000000000) (157072284287 / 250000000000) x90 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx89
  let x91 : ℝ := s⁻¹
  have hx91 : Bounds (1001003005011 / 250000000000) (402008434137 / 100000000000) x91 := by
    apply bounds_inv hs <;> norm_num
  let x92 : ℝ := x90*x91
  have hx92 : Bounds (125729064317 / 50000000000) (1262887661051 / 500000000000) x92 := by
    apply bounds_mul hx90 hx91 <;> norm_num
  let x93 : ℝ := x90/s
  have hx93 : Bounds (125729064317 / 50000000000) (1262887661051 / 500000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(260807 / 1000000)
  have hx95 : Bounds (1260807 / 1000000) (1260807 / 1000000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((260807 / 1000000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(260807 / 1000000)
  have hx96 : Bounds (1260807 / 1000000) (1260807 / 1000000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((260807 / 1000000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (28968999 / 125000000) (231751993 / 1000000000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_12530.1) (by simpa only [div_one] using reflection_log_12530.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (292194533777 / 1000000000000) (292194535039 / 1000000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(260807 / 1000000)
  have hx99 : Bounds (-260807 / 1000000) (-260807 / 1000000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((260807 / 1000000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (739193 / 1000000) (739193 / 1000000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(260807 / 1000000)
  have hx101 : Bounds (739193 / 1000000) (739193 / 1000000) x101 := by
    exact hx100
  let x102 : ℝ := -(260807 / 1000000)
  have hx102 : Bounds (-260807 / 1000000) (-260807 / 1000000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((260807 / 1000000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (739193 / 1000000) (739193 / 1000000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(260807 / 1000000)
  have hx104 : Bounds (739193 / 1000000) (739193 / 1000000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-302196229 / 1000000000) (-75549057 / 250000000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_12531.1) (by simpa only [div_one] using reflection_log_12531.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-13961333569 / 62500000000) (-55845334091 / 250000000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (68813196673 / 1000000000000) (2752527947 / 40000000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (537603099 / 15625000000) (17203299669 / 500000000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (537603099 / 15625000000) (17203299669 / 500000000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-17203299669 / 500000000000) (-537603099 / 15625000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (329370290331 / 500000000000) (82342572833 / 125000000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (329370290331 / 500000000000) (82342572833 / 125000000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (260807 / 1000000)
  have hx114 : Bounds (329370290331 / 500000000000) (82342572833 / 125000000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(261857 / 1000000)
  have hx116 : Bounds (1261857 / 1000000) (1261857 / 1000000) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((261857 / 1000000) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(261857 / 1000000)
  have hx117 : Bounds (1261857 / 1000000) (1261857 / 1000000) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((261857 / 1000000) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (46516889 / 200000000) (116292223 / 500000000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_12532.1) (by simpa only [div_one] using reflection_log_12532.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (146744155007 / 500000000000) (293488311277 / 1000000000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(261857 / 1000000)
  have hx120 : Bounds (-261857 / 1000000) (-261857 / 1000000) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((261857 / 1000000) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (738143 / 1000000) (738143 / 1000000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(261857 / 1000000)
  have hx122 : Bounds (738143 / 1000000) (738143 / 1000000) x122 := by
    exact hx121
  let x123 : ℝ := -(261857 / 1000000)
  have hx123 : Bounds (-261857 / 1000000) (-261857 / 1000000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((261857 / 1000000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (738143 / 1000000) (738143 / 1000000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(261857 / 1000000)
  have hx125 : Bounds (738143 / 1000000) (738143 / 1000000) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-303617707 / 1000000000) (-151808853 / 500000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_12533.1) (by simpa only [div_one] using reflection_log_12533.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-224113285099 / 1000000000000) (-224113284359 / 1000000000000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (13875004983 / 200000000000) (34687513459 / 500000000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (34687512457 / 1000000000000) (34687513459 / 1000000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (34687512457 / 1000000000000) (34687513459 / 1000000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-34687513459 / 1000000000000) (-34687512457 / 1000000000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (658459666541 / 1000000000000) (658459668543 / 1000000000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (658459666541 / 1000000000000) (658459668543 / 1000000000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (261857 / 1000000)
  have hx135 : Bounds (658459666541 / 1000000000000) (658459668543 / 1000000000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(260807 / 1000000)
  have hx136 : Bounds (327910200773 / 500000000000) (41171242777 / 62500000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((260807 / 1000000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(261857 / 1000000)
  have hx137 : Bounds (658460711897 / 1000000000000) (16534798713 / 25000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((261857 / 1000000) : ℝ)) <;> norm_num
  have hc : Bounds (260807 / 1000000) (261857 / 1000000) c := by
    apply contact_bracket hc0 hc1 (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x93 by linarith [hx93.1])
      (show biasE c = x93*c by simpa +zetaDelta only [div_one] using heq)
    · have h1 : x93*(260807 / 1000000) ≤ (41171242777 / 62500000000) := hx136.2
      have h2 : (329370290331 / 500000000000) ≤ biasE (260807 / 1000000) := hx114.1
      linarith
    · have h1 : biasE (261857 / 1000000) ≤ (658459668543 / 1000000000000) := hx135.2
      have h2 : (658460711897 / 1000000000000) ≤ x93*(261857 / 1000000) := hx137.1
      linarith
  let x138 : ℝ := Real.log (2 / 1)
  have hx138 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x138 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x139 : ℝ := (1 / 1)+(261857 / 1000000)
  have hx139 : Bounds (1261857 / 1000000) (1261857 / 1000000) x139 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((261857 / 1000000) : ℝ)) <;> norm_num
  let x140 : ℝ := (1 / 1)+(261857 / 1000000)
  have hx140 : Bounds (1261857 / 1000000) (1261857 / 1000000) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((261857 / 1000000) : ℝ)) <;> norm_num
  let x141 : ℝ := Real.log x140
  have hx141 : Bounds (46516889 / 200000000) (116292223 / 500000000) x141 := by
    exact bounds_log hx140 (by norm_num) (by simpa only [div_one] using reflection_log_12532.1) (by simpa only [div_one] using reflection_log_12532.2)
  let x142 : ℝ := x139*x141
  have hx142 : Bounds (146744155007 / 500000000000) (293488311277 / 1000000000000) x142 := by
    apply bounds_mul hx139 hx141 <;> norm_num
  let x143 : ℝ := -(261857 / 1000000)
  have hx143 : Bounds (-261857 / 1000000) (-261857 / 1000000) x143 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((261857 / 1000000) : ℝ))
  let x144 : ℝ := (1 / 1)+x143
  have hx144 : Bounds (738143 / 1000000) (738143 / 1000000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx143 <;> norm_num
  let x145 : ℝ := (1 / 1)-(261857 / 1000000)
  have hx145 : Bounds (738143 / 1000000) (738143 / 1000000) x145 := by
    exact hx144
  let x146 : ℝ := -(261857 / 1000000)
  have hx146 : Bounds (-261857 / 1000000) (-261857 / 1000000) x146 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((261857 / 1000000) : ℝ))
  let x147 : ℝ := (1 / 1)+x146
  have hx147 : Bounds (738143 / 1000000) (738143 / 1000000) x147 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx146 <;> norm_num
  let x148 : ℝ := (1 / 1)-(261857 / 1000000)
  have hx148 : Bounds (738143 / 1000000) (738143 / 1000000) x148 := by
    exact hx147
  let x149 : ℝ := Real.log x148
  have hx149 : Bounds (-303617707 / 1000000000) (-151808853 / 500000000) x149 := by
    exact bounds_log hx148 (by norm_num) (by simpa only [div_one] using reflection_log_12533.1) (by simpa only [div_one] using reflection_log_12533.2)
  let x150 : ℝ := x145*x149
  have hx150 : Bounds (-224113285099 / 1000000000000) (-224113284359 / 1000000000000) x150 := by
    apply bounds_mul hx145 hx149 <;> norm_num
  let x151 : ℝ := x142+x150
  have hx151 : Bounds (13875004983 / 200000000000) (34687513459 / 500000000000) x151 := by
    apply bounds_add hx142 hx150 <;> norm_num
  let x152 : ℝ := (2 / 1)⁻¹
  have hx152 : Bounds (1 / 2) (1 / 2) x152 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x153 : ℝ := x151*x152
  have hx153 : Bounds (34687512457 / 1000000000000) (34687513459 / 1000000000000) x153 := by
    apply bounds_mul hx151 hx152 <;> norm_num
  let x154 : ℝ := x151/(2 / 1)
  have hx154 : Bounds (34687512457 / 1000000000000) (34687513459 / 1000000000000) x154 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx153
  let x155 : ℝ := -x154
  have hx155 : Bounds (-34687513459 / 1000000000000) (-34687512457 / 1000000000000) x155 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx154
  let x156 : ℝ := x138+x155
  have hx156 : Bounds (658459666541 / 1000000000000) (658459668543 / 1000000000000) x156 := by
    apply bounds_add hx138 hx155 <;> norm_num
  let x157 : ℝ := x138-x154
  have hx157 : Bounds (658459666541 / 1000000000000) (658459668543 / 1000000000000) x157 := by
    exact hx156
  let x158 : ℝ := biasE (261857 / 1000000)
  have hx158 : Bounds (658459666541 / 1000000000000) (658459668543 / 1000000000000) x158 := by
    simpa +zetaDelta only [biasE, div_one] using hx157
  let x159 : ℝ := Real.log (2 / 1)
  have hx159 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x159 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x160 : ℝ := (1 / 1)+(260807 / 1000000)
  have hx160 : Bounds (1260807 / 1000000) (1260807 / 1000000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((260807 / 1000000) : ℝ)) <;> norm_num
  let x161 : ℝ := (1 / 1)+(260807 / 1000000)
  have hx161 : Bounds (1260807 / 1000000) (1260807 / 1000000) x161 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((260807 / 1000000) : ℝ)) <;> norm_num
  let x162 : ℝ := Real.log x161
  have hx162 : Bounds (28968999 / 125000000) (231751993 / 1000000000) x162 := by
    exact bounds_log hx161 (by norm_num) (by simpa only [div_one] using reflection_log_12530.1) (by simpa only [div_one] using reflection_log_12530.2)
  let x163 : ℝ := x160*x162
  have hx163 : Bounds (292194533777 / 1000000000000) (292194535039 / 1000000000000) x163 := by
    apply bounds_mul hx160 hx162 <;> norm_num
  let x164 : ℝ := -(260807 / 1000000)
  have hx164 : Bounds (-260807 / 1000000) (-260807 / 1000000) x164 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((260807 / 1000000) : ℝ))
  let x165 : ℝ := (1 / 1)+x164
  have hx165 : Bounds (739193 / 1000000) (739193 / 1000000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx164 <;> norm_num
  let x166 : ℝ := (1 / 1)-(260807 / 1000000)
  have hx166 : Bounds (739193 / 1000000) (739193 / 1000000) x166 := by
    exact hx165
  let x167 : ℝ := -(260807 / 1000000)
  have hx167 : Bounds (-260807 / 1000000) (-260807 / 1000000) x167 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((260807 / 1000000) : ℝ))
  let x168 : ℝ := (1 / 1)+x167
  have hx168 : Bounds (739193 / 1000000) (739193 / 1000000) x168 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx167 <;> norm_num
  let x169 : ℝ := (1 / 1)-(260807 / 1000000)
  have hx169 : Bounds (739193 / 1000000) (739193 / 1000000) x169 := by
    exact hx168
  let x170 : ℝ := Real.log x169
  have hx170 : Bounds (-302196229 / 1000000000) (-75549057 / 250000000) x170 := by
    exact bounds_log hx169 (by norm_num) (by simpa only [div_one] using reflection_log_12531.1) (by simpa only [div_one] using reflection_log_12531.2)
  let x171 : ℝ := x166*x170
  have hx171 : Bounds (-13961333569 / 62500000000) (-55845334091 / 250000000000) x171 := by
    apply bounds_mul hx166 hx170 <;> norm_num
  let x172 : ℝ := x163+x171
  have hx172 : Bounds (68813196673 / 1000000000000) (2752527947 / 40000000000) x172 := by
    apply bounds_add hx163 hx171 <;> norm_num
  let x173 : ℝ := (2 / 1)⁻¹
  have hx173 : Bounds (1 / 2) (1 / 2) x173 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x174 : ℝ := x172*x173
  have hx174 : Bounds (537603099 / 15625000000) (17203299669 / 500000000000) x174 := by
    apply bounds_mul hx172 hx173 <;> norm_num
  let x175 : ℝ := x172/(2 / 1)
  have hx175 : Bounds (537603099 / 15625000000) (17203299669 / 500000000000) x175 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx174
  let x176 : ℝ := -x175
  have hx176 : Bounds (-17203299669 / 500000000000) (-537603099 / 15625000000) x176 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx175
  let x177 : ℝ := x159+x176
  have hx177 : Bounds (329370290331 / 500000000000) (82342572833 / 125000000000) x177 := by
    apply bounds_add hx159 hx176 <;> norm_num
  let x178 : ℝ := x159-x175
  have hx178 : Bounds (329370290331 / 500000000000) (82342572833 / 125000000000) x178 := by
    exact hx177
  let x179 : ℝ := biasE (260807 / 1000000)
  have hx179 : Bounds (329370290331 / 500000000000) (82342572833 / 125000000000) x179 := by
    simpa +zetaDelta only [biasE, div_one] using hx178
  let x180 : ℝ := biasE c
  have hx180 : Bounds (658459666541 / 1000000000000) (82342572833 / 125000000000) x180 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx158.1 hx179.2
  let x181 : ℝ := Real.log (2 / 1)
  have hx181 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x181 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x182 : ℝ := c*c
  have hx182 : Bounds (68020291249 / 1000000000000) (68569088449 / 1000000000000) x182 := by
    apply bounds_mul hc hc <;> norm_num
  let x183 : ℝ := -x182
  have hx183 : Bounds (-68569088449 / 1000000000000) (-68020291249 / 1000000000000) x183 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx182
  let x184 : ℝ := (1 / 1)+x183
  have hx184 : Bounds (931430911551 / 1000000000000) (931979708751 / 1000000000000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx183 <;> norm_num
  let x185 : ℝ := (1 / 1)-x182
  have hx185 : Bounds (931430911551 / 1000000000000) (931979708751 / 1000000000000) x185 := by
    exact hx184
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (-71033261 / 1000000000) (-17611059 / 250000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_12534.1) (by simpa only [div_one] using reflection_log_12535.2)
  let x187 : ℝ := (2 / 1)⁻¹
  have hx187 : Bounds (1 / 2) (1 / 2) x187 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x188 : ℝ := x186*x187
  have hx188 : Bounds (-71033261 / 2000000000) (-17611059 / 500000000) x188 := by
    apply bounds_mul hx186 hx187 <;> norm_num
  let x189 : ℝ := x186/(2 / 1)
  have hx189 : Bounds (-71033261 / 2000000000) (-17611059 / 500000000) x189 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx188
  let x190 : ℝ := -x189
  have hx190 : Bounds (17611059 / 500000000) (71033261 / 2000000000) x190 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx189
  let x191 : ℝ := x181+x190
  have hx191 : Bounds (364184649 / 500000000) (1457327623 / 2000000000) x191 := by
    apply bounds_add hx181 hx190 <;> norm_num
  let x192 : ℝ := x181-x189
  have hx192 : Bounds (364184649 / 500000000) (1457327623 / 2000000000) x192 := by
    exact hx191
  let x193 : ℝ := c*(1 / 1)
  have hx193 : Bounds (260807 / 1000000) (261857 / 1000000) x193 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x194 : ℝ := c*x193
  have hx194 : Bounds (68020291249 / 1000000000000) (68569088449 / 1000000000000) x194 := by
    apply bounds_mul hc hx193 <;> norm_num
  let x195 : ℝ := c^2
  have hx195 : Bounds (68020291249 / 1000000000000) (68569088449 / 1000000000000) x195 := by
    (convert hx194 using 1; ring)
  let x196 : ℝ := -x195
  have hx196 : Bounds (-68569088449 / 1000000000000) (-68020291249 / 1000000000000) x196 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx195
  let x197 : ℝ := (1 / 1)+x196
  have hx197 : Bounds (931430911551 / 1000000000000) (931979708751 / 1000000000000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx196 <;> norm_num
  let x198 : ℝ := (1 / 1)-x195
  have hx198 : Bounds (931430911551 / 1000000000000) (931979708751 / 1000000000000) x198 := by
    exact hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (1260807 / 1000000) (1261857 / 1000000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-261857 / 1000000) (-260807 / 1000000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (738143 / 1000000) (739193 / 1000000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (738143 / 1000000) (739193 / 1000000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (169103332959 / 125000000000) (54190041767 / 40000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (106603332959 / 62500000000) (34190041767 / 20000000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (106603332959 / 62500000000) (34190041767 / 20000000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (26697411 / 50000000) (67025269 / 125000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_12536.1) (by simpa only [div_one] using reflection_log_12537.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (26697411 / 100000000) (67025269 / 250000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (26697411 / 100000000) (67025269 / 250000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (1 / 1)+a
  have hx210 : Bounds (749 / 500) (1499 / 1000) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) ha <;> norm_num
  let x211 : ℝ := -a
  have hx211 : Bounds (-499 / 1000) (-249 / 500) x211 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg ha
  let x212 : ℝ := (1 / 1)+x211
  have hx212 : Bounds (501 / 1000) (251 / 500) x212 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx211 <;> norm_num
  let x213 : ℝ := (1 / 1)-a
  have hx213 : Bounds (501 / 1000) (251 / 500) x213 := by
    exact hx212
  let x214 : ℝ := x213⁻¹
  have hx214 : Bounds (1992031872509 / 1000000000000) (62375249501 / 31250000000) x214 := by
    apply bounds_inv hx213 <;> norm_num
  let x215 : ℝ := x210*x214
  have hx215 : Bounds (1492031872509 / 500000000000) (46750249501 / 15625000000) x215 := by
    apply bounds_mul hx210 hx214 <;> norm_num
  let x216 : ℝ := x210/x213
  have hx216 : Bounds (1492031872509 / 500000000000) (46750249501 / 15625000000) x216 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx215
  let x217 : ℝ := Real.log x216
  have hx217 : Bounds (1093286043 / 1000000000) (547973699 / 500000000) x217 := by
    exact bounds_log hx216 (by norm_num) (by simpa only [div_one] using reflection_log_12538.1) (by simpa only [div_one] using reflection_log_12539.2)
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (1093286043 / 2000000000) (547973699 / 1000000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (1093286043 / 2000000000) (547973699 / 1000000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := (2 / 1)*x192
  have hx221 : Bounds (364184649 / 250000000) (1457327623 / 1000000000) x221 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x222 : ℝ := c*(1 / 1)
  have hx222 : Bounds (260807 / 1000000) (261857 / 1000000) x222 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x223 : ℝ := c*x222
  have hx223 : Bounds (68020291249 / 1000000000000) (68569088449 / 1000000000000) x223 := by
    apply bounds_mul hc hx222 <;> norm_num
  let x224 : ℝ := c^2
  have hx224 : Bounds (68020291249 / 1000000000000) (68569088449 / 1000000000000) x224 := by
    (convert hx223 using 1; ring)
  let x225 : ℝ := -x224
  have hx225 : Bounds (-68569088449 / 1000000000000) (-68020291249 / 1000000000000) x225 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx224
  let x226 : ℝ := x221+x225
  have hx226 : Bounds (1388169507551 / 1000000000000) (1389307331751 / 1000000000000) x226 := by
    apply bounds_add hx221 hx225 <;> norm_num
  let x227 : ℝ := x221-x224
  have hx227 : Bounds (1388169507551 / 1000000000000) (1389307331751 / 1000000000000) x227 := by
    exact hx226
  let x228 : ℝ := x180*x227
  have hx228 : Bounds (228513407761 / 250000000000) (457596560609 / 500000000000) x228 := by
    apply bounds_mul hx180 hx227 <;> norm_num
  let x229 : ℝ := (2 / 1)*x90
  have hx229 : Bounds (628015418973 / 500000000000) (157072284287 / 125000000000) x229 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x230 : ℝ := x198*(1 / 1)
  have hx230 : Bounds (931430911551 / 1000000000000) (931979708751 / 1000000000000) x230 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x231 : ℝ := x198*x230
  have hx231 : Bounds (54222721437 / 62500000000) (217146544381 / 250000000000) x231 := by
    apply bounds_mul hx198 hx230 <;> norm_num
  let x232 : ℝ := x198^2
  have hx232 : Bounds (54222721437 / 62500000000) (217146544381 / 250000000000) x232 := by
    (convert hx231 using 1; ring)
  let x233 : ℝ := x229*x232
  have hx233 : Bounds (8717492511 / 8000000000) (1091446520031 / 1000000000000) x233 := by
    apply bounds_mul hx229 hx232 <;> norm_num
  let x234 : ℝ := x192*(1 / 1)
  have hx234 : Bounds (364184649 / 500000000) (1457327623 / 2000000000) x234 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x235 : ℝ := x192*x234
  have hx235 : Bounds (530521834269 / 1000000000000) (53095095019 / 100000000000) x235 := by
    apply bounds_mul hx192 hx234 <;> norm_num
  let x236 : ℝ := x192*x235
  have hx236 : Bounds (48301977 / 125000000) (77376948617 / 200000000000) x236 := by
    apply bounds_mul hx192 hx235 <;> norm_num
  let x237 : ℝ := x192^3
  have hx237 : Bounds (48301977 / 125000000) (77376948617 / 200000000000) x237 := by
    (convert hx236 using 1; ring)
  let x238 : ℝ := x233*x237
  have hx238 : Bounds (421072122763 / 1000000000000) (211132003247 / 500000000000) x238 := by
    apply bounds_mul hx233 hx237 <;> norm_num
  let x239 : ℝ := x238⁻¹
  have hx239 : Bounds (1184093345183 / 500000000000) (237489006263 / 100000000000) x239 := by
    apply bounds_inv hx238 <;> norm_num
  let x240 : ℝ := x228*x239
  have hx240 : Bounds (2164649643319 / 1000000000000) (271685381121 / 125000000000) x240 := by
    apply bounds_mul hx228 hx239 <;> norm_num
  let x241 : ℝ := x228/x238
  have hx241 : Bounds (2164649643319 / 1000000000000) (271685381121 / 125000000000) x241 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx240
  let x242 : ℝ := -x209
  have hx242 : Bounds (-67025269 / 250000000) (-26697411 / 100000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x243 : ℝ := (2 / 1)*x192
  have hx243 : Bounds (364184649 / 250000000) (1457327623 / 1000000000) x243 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x244 : ℝ := c*(1 / 1)
  have hx244 : Bounds (260807 / 1000000) (261857 / 1000000) x244 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x245 : ℝ := c*x244
  have hx245 : Bounds (68020291249 / 1000000000000) (68569088449 / 1000000000000) x245 := by
    apply bounds_mul hc hx244 <;> norm_num
  let x246 : ℝ := c^2
  have hx246 : Bounds (68020291249 / 1000000000000) (68569088449 / 1000000000000) x246 := by
    (convert hx245 using 1; ring)
  let x247 : ℝ := -x246
  have hx247 : Bounds (-68569088449 / 1000000000000) (-68020291249 / 1000000000000) x247 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx246
  let x248 : ℝ := x243+x247
  have hx248 : Bounds (1388169507551 / 1000000000000) (1389307331751 / 1000000000000) x248 := by
    apply bounds_add hx243 hx247 <;> norm_num
  let x249 : ℝ := x243-x246
  have hx249 : Bounds (1388169507551 / 1000000000000) (1389307331751 / 1000000000000) x249 := by
    exact hx248
  let x250 : ℝ := x242*x249
  have hx250 : Bounds (-186237395269 / 500000000000) (-370605318807 / 1000000000000) x250 := by
    apply bounds_mul hx242 hx249 <;> norm_num
  let x251 : ℝ := x198⁻¹
  have hx251 : Bounds (26824618353 / 25000000000) (536808467273 / 500000000000) x251 := by
    apply bounds_inv hx198 <;> norm_num
  let x252 : ℝ := c*x251
  have hx252 : Bounds (279841929551 / 1000000000000) (28113410963 / 100000000000) x252 := by
    apply bounds_mul hc hx251 <;> norm_num
  let x253 : ℝ := c/x198
  have hx253 : Bounds (279841929551 / 1000000000000) (28113410963 / 100000000000) x253 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx252
  let x254 : ℝ := (2 / 1)*x253
  have hx254 : Bounds (279841929551 / 500000000000) (28113410963 / 50000000000) x254 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx253 <;> norm_num
  let x255 : ℝ := (2 / 1)*c
  have hx255 : Bounds (260807 / 500000) (261857 / 500000) x255 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hc <;> norm_num
  let x256 : ℝ := -x255
  have hx256 : Bounds (-261857 / 500000) (-260807 / 500000) x256 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx255
  let x257 : ℝ := x254+x256
  have hx257 : Bounds (17984929551 / 500000000000) (2032710963 / 50000000000) x257 := by
    apply bounds_add hx254 hx256 <;> norm_num
  let x258 : ℝ := x254-x255
  have hx258 : Bounds (17984929551 / 500000000000) (2032710963 / 50000000000) x258 := by
    exact hx257
  let x259 : ℝ := x180*x258
  have hx259 : Bounds (23684701429 / 1000000000000) (6695146021 / 250000000000) x259 := by
    apply bounds_mul hx180 hx258 <;> norm_num
  let x260 : ℝ := x250+x259
  have hx260 : Bounds (-348790089109 / 1000000000000) (-343824734723 / 1000000000000) x260 := by
    apply bounds_add hx250 hx259 <;> norm_num
  let x261 : ℝ := (2 / 1)*x90
  have hx261 : Bounds (628015418973 / 500000000000) (157072284287 / 125000000000) x261 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x262 : ℝ := x198*(1 / 1)
  have hx262 : Bounds (931430911551 / 1000000000000) (931979708751 / 1000000000000) x262 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x263 : ℝ := x198*x262
  have hx263 : Bounds (54222721437 / 62500000000) (217146544381 / 250000000000) x263 := by
    apply bounds_mul hx198 hx262 <;> norm_num
  let x264 : ℝ := x198^2
  have hx264 : Bounds (54222721437 / 62500000000) (217146544381 / 250000000000) x264 := by
    (convert hx263 using 1; ring)
  let x265 : ℝ := x261*x264
  have hx265 : Bounds (8717492511 / 8000000000) (1091446520031 / 1000000000000) x265 := by
    apply bounds_mul hx261 hx264 <;> norm_num
  let x266 : ℝ := x192*(1 / 1)
  have hx266 : Bounds (364184649 / 500000000) (1457327623 / 2000000000) x266 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x267 : ℝ := x192*x266
  have hx267 : Bounds (530521834269 / 1000000000000) (53095095019 / 100000000000) x267 := by
    apply bounds_mul hx192 hx266 <;> norm_num
  let x268 : ℝ := x192*x267
  have hx268 : Bounds (48301977 / 125000000) (77376948617 / 200000000000) x268 := by
    apply bounds_mul hx192 hx267 <;> norm_num
  let x269 : ℝ := x192^3
  have hx269 : Bounds (48301977 / 125000000) (77376948617 / 200000000000) x269 := by
    (convert hx268 using 1; ring)
  let x270 : ℝ := x265*x269
  have hx270 : Bounds (421072122763 / 1000000000000) (211132003247 / 500000000000) x270 := by
    apply bounds_mul hx265 hx269 <;> norm_num
  let x271 : ℝ := x270⁻¹
  have hx271 : Bounds (1184093345183 / 500000000000) (237489006263 / 100000000000) x271 := by
    apply bounds_inv hx270 <;> norm_num
  let x272 : ℝ := x260*x271
  have hx272 : Bounds (-828338116569 / 1000000000000) (-814241160589 / 1000000000000) x272 := by
    apply bounds_mul hx260 hx271 <;> norm_num
  let x273 : ℝ := x260/x270
  have hx273 : Bounds (-828338116569 / 1000000000000) (-814241160589 / 1000000000000) x273 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx272
  let x274 : ℝ := (4 / 1)*c
  have hx274 : Bounds (260807 / 250000) (261857 / 250000) x274 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hc <;> norm_num
  let x275 : ℝ := x198⁻¹
  have hx275 : Bounds (26824618353 / 25000000000) (536808467273 / 500000000000) x275 := by
    apply bounds_inv hx198 <;> norm_num
  let x276 : ℝ := x274*x275
  have hx276 : Bounds (559683859103 / 500000000000) (562268219259 / 500000000000) x276 := by
    apply bounds_mul hx274 hx275 <;> norm_num
  let x277 : ℝ := x274/x198
  have hx277 : Bounds (559683859103 / 500000000000) (562268219259 / 500000000000) x277 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx276
  let x278 : ℝ := (3 / 1)*c
  have hx278 : Bounds (782421 / 1000000) (785571 / 1000000) x278 := by
    apply bounds_mul (bounds_const ((3 / 1) : ℝ)) hc <;> norm_num
  let x279 : ℝ := x198*x192
  have hx279 : Bounds (678425679181 / 1000000000000) (33954994341 / 50000000000) x279 := by
    apply bounds_mul hx198 hx192 <;> norm_num
  let x280 : ℝ := x279⁻¹
  have hx280 : Bounds (1472537426979 / 1000000000000) (1474000809061 / 1000000000000) x280 := by
    apply bounds_inv hx279 <;> norm_num
  let x281 : ℝ := x278*x280
  have hx281 : Bounds (576072103077 / 500000000000) (46317291583 / 40000000000) x281 := by
    apply bounds_mul hx278 hx280 <;> norm_num
  let x282 : ℝ := x278/x279
  have hx282 : Bounds (576072103077 / 500000000000) (46317291583 / 40000000000) x282 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx281
  let x283 : ℝ := -x282
  have hx283 : Bounds (-46317291583 / 40000000000) (-576072103077 / 500000000000) x283 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx282
  let x284 : ℝ := x277+x283
  have hx284 : Bounds (-38564571369 / 1000000000000) (-6901941909 / 250000000000) x284 := by
    apply bounds_add hx277 hx283 <;> norm_num
  let x285 : ℝ := x277-x282
  have hx285 : Bounds (-38564571369 / 1000000000000) (-6901941909 / 250000000000) x285 := by
    exact hx284
  let x286 : ℝ := x241*x285
  have hx286 : Bounds (-41909721081 / 500000000000) (-29880572183 / 500000000000) x286 := by
    apply bounds_mul hx241 hx285 <;> norm_num
  let x287 : ℝ := x273+x286
  have hx287 : Bounds (-912157558731 / 1000000000000) (-174800460991 / 200000000000) x287 := by
    apply bounds_add hx273 hx286 <;> norm_num
  let x288 : ℝ := (2 / 1)*x192
  have hx288 : Bounds (364184649 / 250000000) (1457327623 / 1000000000) x288 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x289 : ℝ := c*(1 / 1)
  have hx289 : Bounds (260807 / 1000000) (261857 / 1000000) x289 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x290 : ℝ := c*x289
  have hx290 : Bounds (68020291249 / 1000000000000) (68569088449 / 1000000000000) x290 := by
    apply bounds_mul hc hx289 <;> norm_num
  let x291 : ℝ := c^2
  have hx291 : Bounds (68020291249 / 1000000000000) (68569088449 / 1000000000000) x291 := by
    (convert hx290 using 1; ring)
  let x292 : ℝ := -x291
  have hx292 : Bounds (-68569088449 / 1000000000000) (-68020291249 / 1000000000000) x292 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx291
  let x293 : ℝ := x288+x292
  have hx293 : Bounds (1388169507551 / 1000000000000) (1389307331751 / 1000000000000) x293 := by
    apply bounds_add hx288 hx292 <;> norm_num
  let x294 : ℝ := x288-x291
  have hx294 : Bounds (1388169507551 / 1000000000000) (1389307331751 / 1000000000000) x294 := by
    exact hx293
  let x295 : ℝ := c*x294
  have hx295 : Bounds (72408864951 / 200000000000) (363799849971 / 1000000000000) x295 := by
    apply bounds_mul hc hx294 <;> norm_num
  let x296 : ℝ := x198*(1 / 1)
  have hx296 : Bounds (931430911551 / 1000000000000) (931979708751 / 1000000000000) x296 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x297 : ℝ := x198*x296
  have hx297 : Bounds (54222721437 / 62500000000) (217146544381 / 250000000000) x297 := by
    apply bounds_mul hx198 hx296 <;> norm_num
  let x298 : ℝ := x198^2
  have hx298 : Bounds (54222721437 / 62500000000) (217146544381 / 250000000000) x298 := by
    (convert hx297 using 1; ring)
  let x299 : ℝ := x192*(1 / 1)
  have hx299 : Bounds (364184649 / 500000000) (1457327623 / 2000000000) x299 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x300 : ℝ := x192*x299
  have hx300 : Bounds (530521834269 / 1000000000000) (53095095019 / 100000000000) x300 := by
    apply bounds_mul hx192 hx299 <;> norm_num
  let x301 : ℝ := x192^2
  have hx301 : Bounds (530521834269 / 1000000000000) (53095095019 / 100000000000) x301 := by
    (convert hx300 using 1; ring)
  let x302 : ℝ := x298*x301
  have hx302 : Bounds (460261402173 / 1000000000000) (461176656279 / 1000000000000) x302 := by
    apply bounds_mul hx298 hx301 <;> norm_num
  let x303 : ℝ := x302⁻¹
  have hx303 : Bounds (433673294771 / 200000000000) (2172678385107 / 1000000000000) x303 := by
    apply bounds_inv hx302 <;> norm_num
  let x304 : ℝ := x295*x303
  have hx304 : Bounds (98130596981 / 125000000000) (395210035269 / 500000000000) x304 := by
    apply bounds_mul hx295 hx303 <;> norm_num
  let x305 : ℝ := x295/x302
  have hx305 : Bounds (98130596981 / 125000000000) (395210035269 / 500000000000) x305 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx304
  let x306 : ℝ := c*x220
  have hx306 : Bounds (35642081627 / 250000000000) (1434907489 / 10000000000) x306 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x307 : ℝ := x180+x306
  have hx307 : Bounds (801027993049 / 1000000000000) (200557832891 / 250000000000) x307 := by
    apply bounds_add hx180 hx306 <;> norm_num
  let x308 : ℝ := x307*(1 / 1)
  have hx308 : Bounds (801027993049 / 1000000000000) (200557832891 / 250000000000) x308 := by
    apply bounds_mul hx307 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x309 : ℝ := x307*x308
  have hx309 : Bounds (40102865353 / 62500000000) (643575109343 / 1000000000000) x309 := by
    apply bounds_mul hx307 hx308 <;> norm_num
  let x310 : ℝ := x307^2
  have hx310 : Bounds (40102865353 / 62500000000) (643575109343 / 1000000000000) x310 := by
    (convert hx309 using 1; ring)
  let x311 : ℝ := x287*x310
  have hx311 : Bounds (-587041900599 / 1000000000000) (-560799948061 / 1000000000000) x311 := by
    apply bounds_mul hx287 hx310 <;> norm_num
  let x312 : ℝ := (2 / 1)*x241
  have hx312 : Bounds (2164649643319 / 500000000000) (271685381121 / 62500000000) x312 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx241 <;> norm_num
  let x313 : ℝ := c*x220
  have hx313 : Bounds (35642081627 / 250000000000) (1434907489 / 10000000000) x313 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x314 : ℝ := x180+x313
  have hx314 : Bounds (801027993049 / 1000000000000) (200557832891 / 250000000000) x314 := by
    apply bounds_add hx180 hx313 <;> norm_num
  let x315 : ℝ := x312*x314
  have hx315 : Bounds (866972479721 / 250000000000) (3487272401011 / 1000000000000) x315 := by
    apply bounds_mul hx312 hx314 <;> norm_num
  let x316 : ℝ := -x209
  have hx316 : Bounds (-67025269 / 250000000) (-26697411 / 100000000) x316 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x317 : ℝ := x220+x316
  have hx317 : Bounds (557083891 / 2000000000) (280999589 / 1000000000) x317 := by
    apply bounds_add hx220 hx316 <;> norm_num
  let x318 : ℝ := x220-x209
  have hx318 : Bounds (557083891 / 2000000000) (280999589 / 1000000000) x318 := by
    exact hx317
  let x319 : ℝ := x315*x318
  have hx319 : Bounds (193190560957 / 200000000000) (122490263927 / 125000000000) x319 := by
    apply bounds_mul hx315 hx318 <;> norm_num
  let x320 : ℝ := x311+x319
  have hx320 : Bounds (189455452093 / 500000000000) (83824432671 / 200000000000) x320 := by
    apply bounds_add hx311 hx319 <;> norm_num
  let x321 : ℝ := a*(1 / 1)
  have hx321 : Bounds (249 / 500) (499 / 1000) x321 := by
    apply bounds_mul ha (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x322 : ℝ := a*x321
  have hx322 : Bounds (62001 / 250000) (249001 / 1000000) x322 := by
    apply bounds_mul ha hx321 <;> norm_num
  let x323 : ℝ := a^2
  have hx323 : Bounds (62001 / 250000) (249001 / 1000000) x323 := by
    (convert hx322 using 1; ring)
  let x324 : ℝ := -x323
  have hx324 : Bounds (-249001 / 1000000) (-62001 / 250000) x324 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx323
  let x325 : ℝ := (1 / 1)+x324
  have hx325 : Bounds (750999 / 1000000) (187999 / 250000) x325 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx324 <;> norm_num
  let x326 : ℝ := (1 / 1)-x323
  have hx326 : Bounds (750999 / 1000000) (187999 / 250000) x326 := by
    exact hx325
  let x327 : ℝ := x326⁻¹
  have hx327 : Bounds (166224288427 / 125000000000) (1331559695819 / 1000000000000) x327 := by
    apply bounds_inv hx326 <;> norm_num
  let x328 : ℝ := (1 / 1)*x327
  have hx328 : Bounds (166224288427 / 125000000000) (1331559695819 / 1000000000000) x328 := by
    apply bounds_mul (bounds_const ((1 / 1) : ℝ)) hx327 <;> norm_num
  let x329 : ℝ := (1 / 1)/x326
  have hx329 : Bounds (166224288427 / 125000000000) (1331559695819 / 1000000000000) x329 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx328
  let x330 : ℝ := x329*x305
  have hx330 : Bounds (1043948073989 / 1000000000000) (210498301739 / 200000000000) x330 := by
    apply bounds_mul hx329 hx305 <;> norm_num
  let x331 : ℝ := x320+x330
  have hx331 : Bounds (56914359127 / 40000000000) (29432273441 / 20000000000) x331 := by
    apply bounds_add hx320 hx330 <;> norm_num
  let x332 : ℝ := x180*(1 / 1)
  have hx332 : Bounds (658459666541 / 1000000000000) (82342572833 / 125000000000) x332 := by
    apply bounds_mul hx180 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x333 : ℝ := x180*x332
  have hx333 : Bounds (433569132461 / 1000000000000) (433939155249 / 1000000000000) x333 := by
    apply bounds_mul hx180 hx332 <;> norm_num
  let x334 : ℝ := x180^2
  have hx334 : Bounds (433569132461 / 1000000000000) (433939155249 / 1000000000000) x334 := by
    (convert hx333 using 1; ring)
  let x335 : ℝ := x331*x334
  have hx335 : Bounds (616907732781 / 1000000000000) (638590793703 / 1000000000000) x335 := by
    apply bounds_mul hx331 hx334 <;> norm_num
  let x336 : ℝ := x90*x192
  have hx336 : Bounds (9148542997 / 20000000000) (457811557399 / 1000000000000) x336 := by
    apply bounds_mul hx90 hx192 <;> norm_num
  let x337 : ℝ := x336⁻¹
  have hx337 : Bounds (2184304838613 / 1000000000000) (2186140460461 / 1000000000000) x337 := by
    apply bounds_inv hx336 <;> norm_num
  let x338 : ℝ := x335*x337
  have hx338 : Bounds (1347514545691 / 1000000000000) (1396049171793 / 1000000000000) x338 := by
    apply bounds_mul hx335 hx337 <;> norm_num
  let x339 : ℝ := x335/x336
  have hx339 : Bounds (1347514545691 / 1000000000000) (1396049171793 / 1000000000000) x339 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx338
  have hu : x339 < (111591437014759247003793 / 70687248002000000000000) := lt_of_le_of_lt hx339.2 (by norm_num)
  simpa +zetaDelta only [ScFormula,Kprime,K,Mprime,SmallMean.A,biasB,div_one,pow_two] using hu

open GeneralCK.Reflection
/-- Uniform derivative enclosure including input boxes with z=0. -/
theorem derivative_bound_898 {a z s : ℝ}
    (ha : a ∈ Set.Icc ((249 / 500):ℝ) ((499 / 1000)))
    (hz : z ∈ Set.Icc (0:ℝ) (1/1000))
    (hs : s ∈ Set.Ioo (a*(1-z)/2) (a*(1+z)/2)) :
    P a ((biasE a+biasE (a*z))/2) s ≤ (111591437014759247003793 / 70687248002000000000000) := by
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
  have hsl : (248751 / 1000000) ≤ s := by
    have h := mul_le_mul ha.1 (show (999/1000:ℝ) ≤ 1-z by linarith [hz.2])
      (by norm_num : (0:ℝ) ≤ 999/1000) ha0.le
    nlinarith [hs.1]
  have hsu : s ≤ (499499 / 2000000) := by
    have h := mul_le_mul ha.2 (show 1+z ≤ (1001/1000:ℝ) by linarith [hz.2])
      (by linarith [hz.1] : 0 ≤ 1+z) (by norm_num : (0:ℝ) ≤ (499 / 1000))
    nlinarith [hs.2]
  have hy := div_pos he hs0
  have hc := biasContact_mem hy
  have heq : biasE (biasContact (((biasE a+biasE (a*z))/2)/s)) =
      (((biasE a+biasE (a*z))/2)/s)*biasContact (((biasE a+biasE (a*z))/2)/s) := by
    exact (div_eq_iff hc.1.ne').mp (biasR_biasContact hy)
  have hb := derivative_leaf_898 a z s _ ha hz ⟨hsl,hsu⟩ hc.1.le hc.2.le heq
  rw [P_eq_formula ha0 ha1 he hs0]
  exact hb.le

/-- Checked low-ratio strip: includes arbitrarily small positive z. -/
theorem curvature_leaf_898 {a z : ℝ}
    (ha : a ∈ Set.Icc ((249 / 500):ℝ) ((499 / 1000)))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < curvature a (a*z) := by
  have ha0 : 0 < a := by linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  apply curvature_pos_of_derivative_bound ha0 ha1 hz.1 (by linarith [hz.2])
    (fun s hs => derivative_bound_898 ha ⟨hz.1.le,hz.2⟩ hs) (M := (111591437014759247003793 / 70687248002000000000000))
  exact lt_of_lt_of_le (by norm_num : (111591437014759247003793 / 70687248002000000000000) < 2*((249 / 500):ℝ)/(1-((249 / 500):ℝ)^2)^2)
    (base_mono (by norm_num) ha.1 ha1)

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Cell0899 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
theorem derivative_leaf_899 (a z s c : ℝ)
    (ha : Bounds (499 / 1000) (1 / 2) a) (hz : Bounds 0 (1/1000) z)
    (hs : Bounds (498501 / 2000000) (1001 / 4000) s) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (heq : biasE c = (((biasE a+biasE (a*z))/2)/s)*c) :
    ScFormula c a ((biasE a+biasE (a*z))/2)*(biasE c)^2 /
      (((biasE a+biasE (a*z))/2)*biasB c) < (894075455392128665381569 / 563999498001000000000000) := by
  let x0 : ℝ := Real.log (2 / 1)
  have hx0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x0 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x1 : ℝ := (1 / 1)+(1 / 2)
  have hx1 : Bounds (3 / 2) (3 / 2) x1 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1 / 2) : ℝ)) <;> norm_num
  let x2 : ℝ := (1 / 1)+(1 / 2)
  have hx2 : Bounds (3 / 2) (3 / 2) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1 / 2) : ℝ)) <;> norm_num
  let x3 : ℝ := Real.log x2
  have hx3 : Bounds (101366277 / 250000000) (405465109 / 1000000000) x3 := by
    exact bounds_log hx2 (by norm_num) (by simpa only [div_one] using reflection_log_6969.1) (by simpa only [div_one] using reflection_log_6969.2)
  let x4 : ℝ := x1*x3
  have hx4 : Bounds (304098831 / 500000000) (1216395327 / 2000000000) x4 := by
    apply bounds_mul hx1 hx3 <;> norm_num
  let x5 : ℝ := -(1 / 2)
  have hx5 : Bounds (-1 / 2) (-1 / 2) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1 / 2) : ℝ))
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (1 / 2) (1 / 2) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-(1 / 2)
  have hx7 : Bounds (1 / 2) (1 / 2) x7 := by
    exact hx6
  let x8 : ℝ := -(1 / 2)
  have hx8 : Bounds (-1 / 2) (-1 / 2) x8 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1 / 2) : ℝ))
  let x9 : ℝ := (1 / 1)+x8
  have hx9 : Bounds (1 / 2) (1 / 2) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx8 <;> norm_num
  let x10 : ℝ := (1 / 1)-(1 / 2)
  have hx10 : Bounds (1 / 2) (1 / 2) x10 := by
    exact hx9
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (-693147181 / 1000000000) (-34657359 / 50000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_12540.1) (by simpa only [div_one] using reflection_log_12540.2)
  let x12 : ℝ := x7*x11
  have hx12 : Bounds (-693147181 / 2000000000) (-34657359 / 100000000) x12 := by
    apply bounds_mul hx7 hx11 <;> norm_num
  let x13 : ℝ := x4+x12
  have hx13 : Bounds (523248143 / 2000000000) (523248147 / 2000000000) x13 := by
    apply bounds_add hx4 hx12 <;> norm_num
  let x14 : ℝ := (2 / 1)⁻¹
  have hx14 : Bounds (1 / 2) (1 / 2) x14 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x15 : ℝ := x13*x14
  have hx15 : Bounds (523248143 / 4000000000) (523248147 / 4000000000) x15 := by
    apply bounds_mul hx13 hx14 <;> norm_num
  let x16 : ℝ := x13/(2 / 1)
  have hx16 : Bounds (523248143 / 4000000000) (523248147 / 4000000000) x16 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx15
  let x17 : ℝ := -x16
  have hx17 : Bounds (-523248147 / 4000000000) (-523248143 / 4000000000) x17 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx16
  let x18 : ℝ := x0+x17
  have hx18 : Bounds (2249340573 / 4000000000) (2249340581 / 4000000000) x18 := by
    apply bounds_add hx0 hx17 <;> norm_num
  let x19 : ℝ := x0-x16
  have hx19 : Bounds (2249340573 / 4000000000) (2249340581 / 4000000000) x19 := by
    exact hx18
  let x20 : ℝ := biasE (1 / 2)
  have hx20 : Bounds (2249340573 / 4000000000) (2249340581 / 4000000000) x20 := by
    simpa +zetaDelta only [biasE, div_one] using hx19
  let x21 : ℝ := Real.log (2 / 1)
  have hx21 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x21 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x22 : ℝ := (1 / 1)+(499 / 1000)
  have hx22 : Bounds (1499 / 1000) (1499 / 1000) x22 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((499 / 1000) : ℝ)) <;> norm_num
  let x23 : ℝ := (1 / 1)+(499 / 1000)
  have hx23 : Bounds (1499 / 1000) (1499 / 1000) x23 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((499 / 1000) : ℝ)) <;> norm_num
  let x24 : ℝ := Real.log x23
  have hx24 : Bounds (404798219 / 1000000000) (20239911 / 50000000) x24 := by
    exact bounds_log hx23 (by norm_num) (by simpa only [div_one] using reflection_log_12526.1) (by simpa only [div_one] using reflection_log_12526.2)
  let x25 : ℝ := x22*x24
  have hx25 : Bounds (606792530281 / 1000000000000) (30339626589 / 50000000000) x25 := by
    apply bounds_mul hx22 hx24 <;> norm_num
  let x26 : ℝ := -(499 / 1000)
  have hx26 : Bounds (-499 / 1000) (-499 / 1000) x26 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((499 / 1000) : ℝ))
  let x27 : ℝ := (1 / 1)+x26
  have hx27 : Bounds (501 / 1000) (501 / 1000) x27 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx26 <;> norm_num
  let x28 : ℝ := (1 / 1)-(499 / 1000)
  have hx28 : Bounds (501 / 1000) (501 / 1000) x28 := by
    exact hx27
  let x29 : ℝ := -(499 / 1000)
  have hx29 : Bounds (-499 / 1000) (-499 / 1000) x29 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((499 / 1000) : ℝ))
  let x30 : ℝ := (1 / 1)+x29
  have hx30 : Bounds (501 / 1000) (501 / 1000) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx29 <;> norm_num
  let x31 : ℝ := (1 / 1)-(499 / 1000)
  have hx31 : Bounds (501 / 1000) (501 / 1000) x31 := by
    exact hx30
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (-345574589 / 500000000) (-691149177 / 1000000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_12527.1) (by simpa only [div_one] using reflection_log_12527.2)
  let x33 : ℝ := x28*x32
  have hx33 : Bounds (-173132869089 / 500000000000) (-346265737677 / 1000000000000) x33 := by
    apply bounds_mul hx28 hx32 <;> norm_num
  let x34 : ℝ := x25+x33
  have hx34 : Bounds (260526792103 / 1000000000000) (260526794103 / 1000000000000) x34 := by
    apply bounds_add hx25 hx33 <;> norm_num
  let x35 : ℝ := (2 / 1)⁻¹
  have hx35 : Bounds (1 / 2) (1 / 2) x35 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x36 : ℝ := x34*x35
  have hx36 : Bounds (130263396051 / 1000000000000) (32565849263 / 250000000000) x36 := by
    apply bounds_mul hx34 hx35 <;> norm_num
  let x37 : ℝ := x34/(2 / 1)
  have hx37 : Bounds (130263396051 / 1000000000000) (32565849263 / 250000000000) x37 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx36
  let x38 : ℝ := -x37
  have hx38 : Bounds (-32565849263 / 250000000000) (-130263396051 / 1000000000000) x38 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx37
  let x39 : ℝ := x21+x38
  have hx39 : Bounds (140720945737 / 250000000000) (562883784949 / 1000000000000) x39 := by
    apply bounds_add hx21 hx38 <;> norm_num
  let x40 : ℝ := x21-x37
  have hx40 : Bounds (140720945737 / 250000000000) (562883784949 / 1000000000000) x40 := by
    exact hx39
  let x41 : ℝ := biasE (499 / 1000)
  have hx41 : Bounds (140720945737 / 250000000000) (562883784949 / 1000000000000) x41 := by
    simpa +zetaDelta only [biasE, div_one] using hx40
  let x42 : ℝ := biasE a
  have hx42 : Bounds (2249340573 / 4000000000) (562883784949 / 1000000000000) x42 := by
    exact bounds_biasE ha (by norm_num) (by norm_num) hx20.1 hx41.2
  let x43 : ℝ := a*z
  have hx43 : Bounds (0 / 1) (1 / 2000) x43 := by
    apply bounds_mul ha hz <;> norm_num
  let x44 : ℝ := Real.log (2 / 1)
  have hx44 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x44 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x45 : ℝ := (1 / 1)+(1 / 2000)
  have hx45 : Bounds (2001 / 2000) (2001 / 2000) x45 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1 / 2000) : ℝ)) <;> norm_num
  let x46 : ℝ := (1 / 1)+(1 / 2000)
  have hx46 : Bounds (2001 / 2000) (2001 / 2000) x46 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1 / 2000) : ℝ)) <;> norm_num
  let x47 : ℝ := Real.log x46
  have hx47 : Bounds (3999 / 8000000) (124969 / 250000000) x47 := by
    exact bounds_log hx46 (by norm_num) (by simpa only [div_one] using reflection_log_12541.1) (by simpa only [div_one] using reflection_log_12541.2)
  let x48 : ℝ := x45*x47
  have hx48 : Bounds (500124937 / 1000000000000) (250062969 / 500000000000) x48 := by
    apply bounds_mul hx45 hx47 <;> norm_num
  let x49 : ℝ := -(1 / 2000)
  have hx49 : Bounds (-1 / 2000) (-1 / 2000) x49 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1 / 2000) : ℝ))
  let x50 : ℝ := (1 / 1)+x49
  have hx50 : Bounds (1999 / 2000) (1999 / 2000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx49 <;> norm_num
  let x51 : ℝ := (1 / 1)-(1 / 2000)
  have hx51 : Bounds (1999 / 2000) (1999 / 2000) x51 := by
    exact hx50
  let x52 : ℝ := -(1 / 2000)
  have hx52 : Bounds (-1 / 2000) (-1 / 2000) x52 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1 / 2000) : ℝ))
  let x53 : ℝ := (1 / 1)+x52
  have hx53 : Bounds (1999 / 2000) (1999 / 2000) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx52 <;> norm_num
  let x54 : ℝ := (1 / 1)-(1 / 2000)
  have hx54 : Bounds (1999 / 2000) (1999 / 2000) x54 := by
    exact hx53
  let x55 : ℝ := Real.log x54
  have hx55 : Bounds (-250063 / 500000000) (-4001 / 8000000) x55 := by
    exact bounds_log hx54 (by norm_num) (by simpa only [div_one] using reflection_log_12542.1) (by simpa only [div_one] using reflection_log_12542.2)
  let x56 : ℝ := x51*x55
  have hx56 : Bounds (-499875937 / 1000000000000) (-499874937 / 1000000000000) x56 := by
    apply bounds_mul hx51 hx55 <;> norm_num
  let x57 : ℝ := x48+x56
  have hx57 : Bounds (249 / 1000000000) (251001 / 1000000000000) x57 := by
    apply bounds_add hx48 hx56 <;> norm_num
  let x58 : ℝ := (2 / 1)⁻¹
  have hx58 : Bounds (1 / 2) (1 / 2) x58 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x59 : ℝ := x57*x58
  have hx59 : Bounds (249 / 2000000000) (125501 / 1000000000000) x59 := by
    apply bounds_mul hx57 hx58 <;> norm_num
  let x60 : ℝ := x57/(2 / 1)
  have hx60 : Bounds (249 / 2000000000) (125501 / 1000000000000) x60 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx59
  let x61 : ℝ := -x60
  have hx61 : Bounds (-125501 / 1000000000000) (-249 / 2000000000) x61 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx60
  let x62 : ℝ := x44+x61
  have hx62 : Bounds (693147054499 / 1000000000000) (1386294113 / 2000000000) x62 := by
    apply bounds_add hx44 hx61 <;> norm_num
  let x63 : ℝ := x44-x60
  have hx63 : Bounds (693147054499 / 1000000000000) (1386294113 / 2000000000) x63 := by
    exact hx62
  let x64 : ℝ := biasE (1 / 2000)
  have hx64 : Bounds (693147054499 / 1000000000000) (1386294113 / 2000000000) x64 := by
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
  have hx86 : Bounds (693147054499 / 1000000000000) (693147181 / 1000000000) x86 := by
    exact bounds_biasE hx43 (by norm_num) (by norm_num) hx64.1 hx85.2
  let x87 : ℝ := x42+x86
  have hx87 : Bounds (1255482197749 / 1000000000000) (1256030965949 / 1000000000000) x87 := by
    apply bounds_add hx42 hx86 <;> norm_num
  let x88 : ℝ := (2 / 1)⁻¹
  have hx88 : Bounds (1 / 2) (1 / 2) x88 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x89 : ℝ := x87*x88
  have hx89 : Bounds (313870549437 / 500000000000) (25120619319 / 40000000000) x89 := by
    apply bounds_mul hx87 hx88 <;> norm_num
  let x90 : ℝ := x87/(2 / 1)
  have hx90 : Bounds (313870549437 / 500000000000) (25120619319 / 40000000000) x90 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx89
  let x91 : ℝ := s⁻¹
  have hx91 : Bounds (3996003996003 / 1000000000000) (32096224481 / 8000000000) x91 := by
    apply bounds_inv hs <;> norm_num
  let x92 : ℝ := x90*x91
  have hx92 : Bounds (501691187911 / 200000000000) (2519615739889 / 1000000000000) x92 := by
    apply bounds_mul hx90 hx91 <;> norm_num
  let x93 : ℝ := x90/s
  have hx93 : Bounds (501691187911 / 200000000000) (2519615739889 / 1000000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(261383 / 1000000)
  have hx95 : Bounds (1261383 / 1000000) (1261383 / 1000000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((261383 / 1000000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(261383 / 1000000)
  have hx96 : Bounds (1261383 / 1000000) (1261383 / 1000000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((261383 / 1000000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (116104369 / 500000000) (232208739 / 1000000000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_12543.1) (by simpa only [div_one] using reflection_log_12543.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (73226038641 / 250000000000) (292904155827 / 1000000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(261383 / 1000000)
  have hx99 : Bounds (-261383 / 1000000) (-261383 / 1000000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((261383 / 1000000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (738617 / 1000000) (738617 / 1000000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(261383 / 1000000)
  have hx101 : Bounds (738617 / 1000000) (738617 / 1000000) x101 := by
    exact hx100
  let x102 : ℝ := -(261383 / 1000000)
  have hx102 : Bounds (-261383 / 1000000) (-261383 / 1000000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((261383 / 1000000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (738617 / 1000000) (738617 / 1000000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(261383 / 1000000)
  have hx104 : Bounds (738617 / 1000000) (738617 / 1000000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-302975761 / 1000000000) (-3787197 / 12500000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_12544.1) (by simpa only [div_one] using reflection_log_12544.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-223783047663 / 1000000000000) (-223783046923 / 1000000000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (69121106901 / 1000000000000) (8640138613 / 125000000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (691211069 / 20000000000) (8640138613 / 250000000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (691211069 / 20000000000) (8640138613 / 250000000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-8640138613 / 250000000000) (-691211069 / 20000000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (164646656387 / 250000000000) (13171732551 / 20000000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (164646656387 / 250000000000) (13171732551 / 20000000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (261383 / 1000000)
  have hx114 : Bounds (164646656387 / 250000000000) (13171732551 / 20000000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(52487 / 200000)
  have hx116 : Bounds (252487 / 200000) (252487 / 200000) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((52487 / 200000) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(52487 / 200000)
  have hx117 : Bounds (252487 / 200000) (252487 / 200000) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((52487 / 200000) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (46608479 / 200000000) (58260599 / 250000000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_12545.1) (by simpa only [div_one] using reflection_log_12545.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (294200875931 / 1000000000000) (58840175439 / 200000000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(52487 / 200000)
  have hx120 : Bounds (-52487 / 200000) (-52487 / 200000) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((52487 / 200000) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (147513 / 200000) (147513 / 200000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(52487 / 200000)
  have hx122 : Bounds (147513 / 200000) (147513 / 200000) x122 := by
    exact hx121
  let x123 : ℝ := -(52487 / 200000)
  have hx123 : Bounds (-52487 / 200000) (-52487 / 200000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((52487 / 200000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (147513 / 200000) (147513 / 200000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(52487 / 200000)
  have hx125 : Bounds (147513 / 200000) (147513 / 200000) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-15220053 / 50000000) (-304401059 / 1000000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_12546.1) (by simpa only [div_one] using reflection_log_12546.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-224515567819 / 1000000000000) (-224515567081 / 1000000000000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (4355331757 / 62500000000) (34842655057 / 500000000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (4355331757 / 125000000000) (34842655057 / 1000000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (4355331757 / 125000000000) (34842655057 / 1000000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-34842655057 / 1000000000000) (-4355331757 / 125000000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (658304524943 / 1000000000000) (20572016467 / 31250000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (658304524943 / 1000000000000) (20572016467 / 31250000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (52487 / 200000)
  have hx135 : Bounds (658304524943 / 1000000000000) (20572016467 / 31250000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(261383 / 1000000)
  have hx136 : Bounds (20489616839 / 31250000000) (32929236047 / 50000000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((261383 / 1000000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(52487 / 200000)
  have hx137 : Bounds (658306634497 / 1000000000000) (330617678349 / 500000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((52487 / 200000) : ℝ)) <;> norm_num
  have hc : Bounds (261383 / 1000000) (52487 / 200000) c := by
    apply contact_bracket hc0 hc1 (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x93 by linarith [hx93.1])
      (show biasE c = x93*c by simpa +zetaDelta only [div_one] using heq)
    · have h1 : x93*(261383 / 1000000) ≤ (32929236047 / 50000000000) := hx136.2
      have h2 : (164646656387 / 250000000000) ≤ biasE (261383 / 1000000) := hx114.1
      linarith
    · have h1 : biasE (52487 / 200000) ≤ (20572016467 / 31250000000) := hx135.2
      have h2 : (658306634497 / 1000000000000) ≤ x93*(52487 / 200000) := hx137.1
      linarith
  let x138 : ℝ := Real.log (2 / 1)
  have hx138 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x138 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x139 : ℝ := (1 / 1)+(52487 / 200000)
  have hx139 : Bounds (252487 / 200000) (252487 / 200000) x139 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((52487 / 200000) : ℝ)) <;> norm_num
  let x140 : ℝ := (1 / 1)+(52487 / 200000)
  have hx140 : Bounds (252487 / 200000) (252487 / 200000) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((52487 / 200000) : ℝ)) <;> norm_num
  let x141 : ℝ := Real.log x140
  have hx141 : Bounds (46608479 / 200000000) (58260599 / 250000000) x141 := by
    exact bounds_log hx140 (by norm_num) (by simpa only [div_one] using reflection_log_12545.1) (by simpa only [div_one] using reflection_log_12545.2)
  let x142 : ℝ := x139*x141
  have hx142 : Bounds (294200875931 / 1000000000000) (58840175439 / 200000000000) x142 := by
    apply bounds_mul hx139 hx141 <;> norm_num
  let x143 : ℝ := -(52487 / 200000)
  have hx143 : Bounds (-52487 / 200000) (-52487 / 200000) x143 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((52487 / 200000) : ℝ))
  let x144 : ℝ := (1 / 1)+x143
  have hx144 : Bounds (147513 / 200000) (147513 / 200000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx143 <;> norm_num
  let x145 : ℝ := (1 / 1)-(52487 / 200000)
  have hx145 : Bounds (147513 / 200000) (147513 / 200000) x145 := by
    exact hx144
  let x146 : ℝ := -(52487 / 200000)
  have hx146 : Bounds (-52487 / 200000) (-52487 / 200000) x146 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((52487 / 200000) : ℝ))
  let x147 : ℝ := (1 / 1)+x146
  have hx147 : Bounds (147513 / 200000) (147513 / 200000) x147 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx146 <;> norm_num
  let x148 : ℝ := (1 / 1)-(52487 / 200000)
  have hx148 : Bounds (147513 / 200000) (147513 / 200000) x148 := by
    exact hx147
  let x149 : ℝ := Real.log x148
  have hx149 : Bounds (-15220053 / 50000000) (-304401059 / 1000000000) x149 := by
    exact bounds_log hx148 (by norm_num) (by simpa only [div_one] using reflection_log_12546.1) (by simpa only [div_one] using reflection_log_12546.2)
  let x150 : ℝ := x145*x149
  have hx150 : Bounds (-224515567819 / 1000000000000) (-224515567081 / 1000000000000) x150 := by
    apply bounds_mul hx145 hx149 <;> norm_num
  let x151 : ℝ := x142+x150
  have hx151 : Bounds (4355331757 / 62500000000) (34842655057 / 500000000000) x151 := by
    apply bounds_add hx142 hx150 <;> norm_num
  let x152 : ℝ := (2 / 1)⁻¹
  have hx152 : Bounds (1 / 2) (1 / 2) x152 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x153 : ℝ := x151*x152
  have hx153 : Bounds (4355331757 / 125000000000) (34842655057 / 1000000000000) x153 := by
    apply bounds_mul hx151 hx152 <;> norm_num
  let x154 : ℝ := x151/(2 / 1)
  have hx154 : Bounds (4355331757 / 125000000000) (34842655057 / 1000000000000) x154 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx153
  let x155 : ℝ := -x154
  have hx155 : Bounds (-34842655057 / 1000000000000) (-4355331757 / 125000000000) x155 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx154
  let x156 : ℝ := x138+x155
  have hx156 : Bounds (658304524943 / 1000000000000) (20572016467 / 31250000000) x156 := by
    apply bounds_add hx138 hx155 <;> norm_num
  let x157 : ℝ := x138-x154
  have hx157 : Bounds (658304524943 / 1000000000000) (20572016467 / 31250000000) x157 := by
    exact hx156
  let x158 : ℝ := biasE (52487 / 200000)
  have hx158 : Bounds (658304524943 / 1000000000000) (20572016467 / 31250000000) x158 := by
    simpa +zetaDelta only [biasE, div_one] using hx157
  let x159 : ℝ := Real.log (2 / 1)
  have hx159 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x159 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x160 : ℝ := (1 / 1)+(261383 / 1000000)
  have hx160 : Bounds (1261383 / 1000000) (1261383 / 1000000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((261383 / 1000000) : ℝ)) <;> norm_num
  let x161 : ℝ := (1 / 1)+(261383 / 1000000)
  have hx161 : Bounds (1261383 / 1000000) (1261383 / 1000000) x161 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((261383 / 1000000) : ℝ)) <;> norm_num
  let x162 : ℝ := Real.log x161
  have hx162 : Bounds (116104369 / 500000000) (232208739 / 1000000000) x162 := by
    exact bounds_log hx161 (by norm_num) (by simpa only [div_one] using reflection_log_12543.1) (by simpa only [div_one] using reflection_log_12543.2)
  let x163 : ℝ := x160*x162
  have hx163 : Bounds (73226038641 / 250000000000) (292904155827 / 1000000000000) x163 := by
    apply bounds_mul hx160 hx162 <;> norm_num
  let x164 : ℝ := -(261383 / 1000000)
  have hx164 : Bounds (-261383 / 1000000) (-261383 / 1000000) x164 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((261383 / 1000000) : ℝ))
  let x165 : ℝ := (1 / 1)+x164
  have hx165 : Bounds (738617 / 1000000) (738617 / 1000000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx164 <;> norm_num
  let x166 : ℝ := (1 / 1)-(261383 / 1000000)
  have hx166 : Bounds (738617 / 1000000) (738617 / 1000000) x166 := by
    exact hx165
  let x167 : ℝ := -(261383 / 1000000)
  have hx167 : Bounds (-261383 / 1000000) (-261383 / 1000000) x167 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((261383 / 1000000) : ℝ))
  let x168 : ℝ := (1 / 1)+x167
  have hx168 : Bounds (738617 / 1000000) (738617 / 1000000) x168 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx167 <;> norm_num
  let x169 : ℝ := (1 / 1)-(261383 / 1000000)
  have hx169 : Bounds (738617 / 1000000) (738617 / 1000000) x169 := by
    exact hx168
  let x170 : ℝ := Real.log x169
  have hx170 : Bounds (-302975761 / 1000000000) (-3787197 / 12500000) x170 := by
    exact bounds_log hx169 (by norm_num) (by simpa only [div_one] using reflection_log_12544.1) (by simpa only [div_one] using reflection_log_12544.2)
  let x171 : ℝ := x166*x170
  have hx171 : Bounds (-223783047663 / 1000000000000) (-223783046923 / 1000000000000) x171 := by
    apply bounds_mul hx166 hx170 <;> norm_num
  let x172 : ℝ := x163+x171
  have hx172 : Bounds (69121106901 / 1000000000000) (8640138613 / 125000000000) x172 := by
    apply bounds_add hx163 hx171 <;> norm_num
  let x173 : ℝ := (2 / 1)⁻¹
  have hx173 : Bounds (1 / 2) (1 / 2) x173 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x174 : ℝ := x172*x173
  have hx174 : Bounds (691211069 / 20000000000) (8640138613 / 250000000000) x174 := by
    apply bounds_mul hx172 hx173 <;> norm_num
  let x175 : ℝ := x172/(2 / 1)
  have hx175 : Bounds (691211069 / 20000000000) (8640138613 / 250000000000) x175 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx174
  let x176 : ℝ := -x175
  have hx176 : Bounds (-8640138613 / 250000000000) (-691211069 / 20000000000) x176 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx175
  let x177 : ℝ := x159+x176
  have hx177 : Bounds (164646656387 / 250000000000) (13171732551 / 20000000000) x177 := by
    apply bounds_add hx159 hx176 <;> norm_num
  let x178 : ℝ := x159-x175
  have hx178 : Bounds (164646656387 / 250000000000) (13171732551 / 20000000000) x178 := by
    exact hx177
  let x179 : ℝ := biasE (261383 / 1000000)
  have hx179 : Bounds (164646656387 / 250000000000) (13171732551 / 20000000000) x179 := by
    simpa +zetaDelta only [biasE, div_one] using hx178
  let x180 : ℝ := biasE c
  have hx180 : Bounds (658304524943 / 1000000000000) (13171732551 / 20000000000) x180 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx158.1 hx179.2
  let x181 : ℝ := Real.log (2 / 1)
  have hx181 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x181 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x182 : ℝ := c*c
  have hx182 : Bounds (68321072689 / 1000000000000) (2754885169 / 40000000000) x182 := by
    apply bounds_mul hc hc <;> norm_num
  let x183 : ℝ := -x182
  have hx183 : Bounds (-2754885169 / 40000000000) (-68321072689 / 1000000000000) x183 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx182
  let x184 : ℝ := (1 / 1)+x183
  have hx184 : Bounds (37245114831 / 40000000000) (931678927311 / 1000000000000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx183 <;> norm_num
  let x185 : ℝ := (1 / 1)-x182
  have hx185 : Bounds (37245114831 / 40000000000) (931678927311 / 1000000000000) x185 := by
    exact hx184
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (-8919833 / 125000000) (-35383511 / 500000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_12547.1) (by simpa only [div_one] using reflection_log_12548.2)
  let x187 : ℝ := (2 / 1)⁻¹
  have hx187 : Bounds (1 / 2) (1 / 2) x187 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x188 : ℝ := x186*x187
  have hx188 : Bounds (-8919833 / 250000000) (-35383511 / 1000000000) x188 := by
    apply bounds_mul hx186 hx187 <;> norm_num
  let x189 : ℝ := x186/(2 / 1)
  have hx189 : Bounds (-8919833 / 250000000) (-35383511 / 1000000000) x189 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx188
  let x190 : ℝ := -x189
  have hx190 : Bounds (35383511 / 1000000000) (8919833 / 250000000) x190 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx189
  let x191 : ℝ := x181+x190
  have hx191 : Bounds (728530691 / 1000000000) (728826513 / 1000000000) x191 := by
    apply bounds_add hx181 hx190 <;> norm_num
  let x192 : ℝ := x181-x189
  have hx192 : Bounds (728530691 / 1000000000) (728826513 / 1000000000) x192 := by
    exact hx191
  let x193 : ℝ := c*(1 / 1)
  have hx193 : Bounds (261383 / 1000000) (52487 / 200000) x193 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x194 : ℝ := c*x193
  have hx194 : Bounds (68321072689 / 1000000000000) (2754885169 / 40000000000) x194 := by
    apply bounds_mul hc hx193 <;> norm_num
  let x195 : ℝ := c^2
  have hx195 : Bounds (68321072689 / 1000000000000) (2754885169 / 40000000000) x195 := by
    (convert hx194 using 1; ring)
  let x196 : ℝ := -x195
  have hx196 : Bounds (-2754885169 / 40000000000) (-68321072689 / 1000000000000) x196 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx195
  let x197 : ℝ := (1 / 1)+x196
  have hx197 : Bounds (37245114831 / 40000000000) (931678927311 / 1000000000000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx196 <;> norm_num
  let x198 : ℝ := (1 / 1)-x195
  have hx198 : Bounds (37245114831 / 40000000000) (931678927311 / 1000000000000) x198 := by
    exact hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (1261383 / 1000000) (252487 / 200000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-52487 / 200000) (-261383 / 1000000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (147513 / 200000) (738617 / 1000000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (147513 / 200000) (738617 / 1000000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (676940823187 / 500000000000) (1355812708033 / 1000000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (426940823187 / 250000000000) (855812708033 / 500000000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (426940823187 / 250000000000) (855812708033 / 500000000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (267592249 / 500000000) (107488691 / 200000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_12549.1) (by simpa only [div_one] using reflection_log_12550.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (267592249 / 1000000000) (107488691 / 400000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (267592249 / 1000000000) (107488691 / 400000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (1 / 1)+a
  have hx210 : Bounds (1499 / 1000) (3 / 2) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) ha <;> norm_num
  let x211 : ℝ := -a
  have hx211 : Bounds (-1 / 2) (-499 / 1000) x211 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg ha
  let x212 : ℝ := (1 / 1)+x211
  have hx212 : Bounds (1 / 2) (501 / 1000) x212 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx211 <;> norm_num
  let x213 : ℝ := (1 / 1)-a
  have hx213 : Bounds (1 / 2) (501 / 1000) x213 := by
    exact hx212
  let x214 : ℝ := x213⁻¹
  have hx214 : Bounds (1996007984031 / 1000000000000) (2 / 1) x214 := by
    apply bounds_inv hx213 <;> norm_num
  let x215 : ℝ := x210*x214
  have hx215 : Bounds (1496007984031 / 500000000000) (3 / 1) x215 := by
    apply bounds_mul hx210 hx214 <;> norm_num
  let x216 : ℝ := x210/x213
  have hx216 : Bounds (1496007984031 / 500000000000) (3 / 1) x216 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx215
  let x217 : ℝ := Real.log x216
  have hx217 : Bounds (273986849 / 250000000) (109861229 / 100000000) x217 := by
    exact bounds_log hx216 (by norm_num) (by simpa only [div_one] using reflection_log_12551.1) (by simpa only [div_one] using reflection_log_12552.2)
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (273986849 / 500000000) (109861229 / 200000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (273986849 / 500000000) (109861229 / 200000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := (2 / 1)*x192
  have hx221 : Bounds (728530691 / 500000000) (728826513 / 500000000) x221 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x222 : ℝ := c*(1 / 1)
  have hx222 : Bounds (261383 / 1000000) (52487 / 200000) x222 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x223 : ℝ := c*x222
  have hx223 : Bounds (68321072689 / 1000000000000) (2754885169 / 40000000000) x223 := by
    apply bounds_mul hc hx222 <;> norm_num
  let x224 : ℝ := c^2
  have hx224 : Bounds (68321072689 / 1000000000000) (2754885169 / 40000000000) x224 := by
    (convert hx223 using 1; ring)
  let x225 : ℝ := -x224
  have hx225 : Bounds (-2754885169 / 40000000000) (-68321072689 / 1000000000000) x225 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx224
  let x226 : ℝ := x221+x225
  have hx226 : Bounds (55527570111 / 40000000000) (1389331953311 / 1000000000000) x226 := by
    apply bounds_add hx221 hx225 <;> norm_num
  let x227 : ℝ := x221-x224
  have hx227 : Bounds (55527570111 / 40000000000) (1389331953311 / 1000000000000) x227 := by
    exact hx226
  let x228 : ℝ := x180*x227
  have hx228 : Bounds (913851266579 / 1000000000000) (914995445679 / 1000000000000) x228 := by
    apply bounds_mul hx180 hx227 <;> norm_num
  let x229 : ℝ := (2 / 1)*x90
  have hx229 : Bounds (313870549437 / 250000000000) (25120619319 / 20000000000) x229 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x230 : ℝ := x198*(1 / 1)
  have hx230 : Bounds (37245114831 / 40000000000) (931678927311 / 1000000000000) x230 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x231 : ℝ := x198*x230
  have hx231 : Bounds (866999111733 / 1000000000000) (217006405899 / 250000000000) x231 := by
    apply bounds_mul hx198 hx230 <;> norm_num
  let x232 : ℝ := x198^2
  have hx232 : Bounds (866999111733 / 1000000000000) (217006405899 / 250000000000) x232 := by
    (convert hx231 using 1; ring)
  let x233 : ℝ := x229*x232
  have hx233 : Bounds (272125487561 / 250000000000) (43610682499 / 40000000000) x233 := by
    apply bounds_mul hx229 hx232 <;> norm_num
  let x234 : ℝ := x192*(1 / 1)
  have hx234 : Bounds (728530691 / 1000000000) (728826513 / 1000000000) x234 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x235 : ℝ := x192*x234
  have hx235 : Bounds (33172310483 / 62500000000) (132797021513 / 250000000000) x235 := by
    apply bounds_mul hx192 hx234 <;> norm_num
  let x236 : ℝ := x192*x235
  have hx236 : Bounds (386672740451 / 1000000000000) (77428792101 / 200000000000) x236 := by
    apply bounds_mul hx192 hx235 <;> norm_num
  let x237 : ℝ := x192^3
  have hx237 : Bounds (386672740451 / 1000000000000) (77428792101 / 200000000000) x237 := by
    (convert hx236 using 1; ring)
  let x238 : ℝ := x233*x237
  have hx238 : Bounds (420894032087 / 1000000000000) (16883612343 / 40000000000) x238 := by
    apply bounds_mul hx233 hx237 <;> norm_num
  let x239 : ℝ := x238⁻¹
  have hx239 : Bounds (2369161242711 / 1000000000000) (2375894937359 / 1000000000000) x239 := by
    apply bounds_inv hx238 <;> norm_num
  let x240 : ℝ := x228*x239
  have hx240 : Bounds (2165061002381 / 1000000000000) (271741630887 / 125000000000) x240 := by
    apply bounds_mul hx228 hx239 <;> norm_num
  let x241 : ℝ := x228/x238
  have hx241 : Bounds (2165061002381 / 1000000000000) (271741630887 / 125000000000) x241 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx240
  let x242 : ℝ := -x209
  have hx242 : Bounds (-107488691 / 400000000) (-267592249 / 1000000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x243 : ℝ := (2 / 1)*x192
  have hx243 : Bounds (728530691 / 500000000) (728826513 / 500000000) x243 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x244 : ℝ := c*(1 / 1)
  have hx244 : Bounds (261383 / 1000000) (52487 / 200000) x244 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x245 : ℝ := c*x244
  have hx245 : Bounds (68321072689 / 1000000000000) (2754885169 / 40000000000) x245 := by
    apply bounds_mul hc hx244 <;> norm_num
  let x246 : ℝ := c^2
  have hx246 : Bounds (68321072689 / 1000000000000) (2754885169 / 40000000000) x246 := by
    (convert hx245 using 1; ring)
  let x247 : ℝ := -x246
  have hx247 : Bounds (-2754885169 / 40000000000) (-68321072689 / 1000000000000) x247 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx246
  let x248 : ℝ := x243+x247
  have hx248 : Bounds (55527570111 / 40000000000) (1389331953311 / 1000000000000) x248 := by
    apply bounds_add hx243 hx247 <;> norm_num
  let x249 : ℝ := x243-x246
  have hx249 : Bounds (55527570111 / 40000000000) (1389331953311 / 1000000000000) x249 := by
    exact hx248
  let x250 : ℝ := x242*x249
  have hx250 : Bounds (-74668736513 / 200000000000) (-371468684187 / 1000000000000) x250 := by
    apply bounds_mul hx242 hx249 <;> norm_num
  let x251 : ℝ := x198⁻¹
  have hx251 : Bounds (134166391807 / 125000000000) (214793269837 / 200000000000) x251 := by
    apply bounds_inv hx198 <;> norm_num
  let x252 : ℝ := c*x251
  have hx252 : Bounds (280550511917 / 1000000000000) (281846358849 / 1000000000000) x252 := by
    apply bounds_mul hc hx251 <;> norm_num
  let x253 : ℝ := c/x198
  have hx253 : Bounds (280550511917 / 1000000000000) (281846358849 / 1000000000000) x253 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx252
  let x254 : ℝ := (2 / 1)*x253
  have hx254 : Bounds (280550511917 / 500000000000) (281846358849 / 500000000000) x254 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx253 <;> norm_num
  let x255 : ℝ := (2 / 1)*c
  have hx255 : Bounds (261383 / 500000) (52487 / 100000) x255 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hc <;> norm_num
  let x256 : ℝ := -x255
  have hx256 : Bounds (-52487 / 100000) (-261383 / 500000) x256 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx255
  let x257 : ℝ := x254+x256
  have hx257 : Bounds (18115511917 / 500000000000) (20463358849 / 500000000000) x257 := by
    apply bounds_add hx254 hx256 <;> norm_num
  let x258 : ℝ := x254-x255
  have hx258 : Bounds (18115511917 / 500000000000) (20463358849 / 500000000000) x258 := by
    exact hx257
  let x259 : ℝ := x180*x258
  have hx259 : Bounds (23851046933 / 1000000000000) (13476894493 / 500000000000) x259 := by
    apply bounds_mul hx180 hx258 <;> norm_num
  let x260 : ℝ := x250+x259
  have hx260 : Bounds (-21843289727 / 62500000000) (-344514895201 / 1000000000000) x260 := by
    apply bounds_add hx250 hx259 <;> norm_num
  let x261 : ℝ := (2 / 1)*x90
  have hx261 : Bounds (313870549437 / 250000000000) (25120619319 / 20000000000) x261 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x262 : ℝ := x198*(1 / 1)
  have hx262 : Bounds (37245114831 / 40000000000) (931678927311 / 1000000000000) x262 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x263 : ℝ := x198*x262
  have hx263 : Bounds (866999111733 / 1000000000000) (217006405899 / 250000000000) x263 := by
    apply bounds_mul hx198 hx262 <;> norm_num
  let x264 : ℝ := x198^2
  have hx264 : Bounds (866999111733 / 1000000000000) (217006405899 / 250000000000) x264 := by
    (convert hx263 using 1; ring)
  let x265 : ℝ := x261*x264
  have hx265 : Bounds (272125487561 / 250000000000) (43610682499 / 40000000000) x265 := by
    apply bounds_mul hx261 hx264 <;> norm_num
  let x266 : ℝ := x192*(1 / 1)
  have hx266 : Bounds (728530691 / 1000000000) (728826513 / 1000000000) x266 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x267 : ℝ := x192*x266
  have hx267 : Bounds (33172310483 / 62500000000) (132797021513 / 250000000000) x267 := by
    apply bounds_mul hx192 hx266 <;> norm_num
  let x268 : ℝ := x192*x267
  have hx268 : Bounds (386672740451 / 1000000000000) (77428792101 / 200000000000) x268 := by
    apply bounds_mul hx192 hx267 <;> norm_num
  let x269 : ℝ := x192^3
  have hx269 : Bounds (386672740451 / 1000000000000) (77428792101 / 200000000000) x269 := by
    (convert hx268 using 1; ring)
  let x270 : ℝ := x265*x269
  have hx270 : Bounds (420894032087 / 1000000000000) (16883612343 / 40000000000) x270 := by
    apply bounds_mul hx265 hx269 <;> norm_num
  let x271 : ℝ := x270⁻¹
  have hx271 : Bounds (2369161242711 / 1000000000000) (2375894937359 / 1000000000000) x271 := by
    apply bounds_inv hx270 <;> norm_num
  let x272 : ℝ := x260*x271
  have hx272 : Bounds (-830357783643 / 1000000000000) (-408105668623 / 500000000000) x272 := by
    apply bounds_mul hx260 hx271 <;> norm_num
  let x273 : ℝ := x260/x270
  have hx273 : Bounds (-830357783643 / 1000000000000) (-408105668623 / 500000000000) x273 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx272
  let x274 : ℝ := (4 / 1)*c
  have hx274 : Bounds (261383 / 250000) (52487 / 50000) x274 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hc <;> norm_num
  let x275 : ℝ := x198⁻¹
  have hx275 : Bounds (134166391807 / 125000000000) (214793269837 / 200000000000) x275 := by
    apply bounds_inv hx198 <;> norm_num
  let x276 : ℝ := x274*x275
  have hx276 : Bounds (112220204767 / 100000000000) (563692717697 / 500000000000) x276 := by
    apply bounds_mul hx274 hx275 <;> norm_num
  let x277 : ℝ := x274/x198
  have hx277 : Bounds (112220204767 / 100000000000) (563692717697 / 500000000000) x277 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx276
  let x278 : ℝ := (3 / 1)*c
  have hx278 : Bounds (784149 / 1000000) (157461 / 200000) x278 := by
    apply bounds_mul (bounds_const ((3 / 1) : ℝ)) hc <;> norm_num
  let x279 : ℝ := x198*x192
  have hx279 : Bounds (135671046221 / 200000000000) (169758075957 / 250000000000) x279 := by
    apply bounds_mul hx198 hx192 <;> norm_num
  let x280 : ℝ := x279⁻¹
  have hx280 : Bounds (736341993129 / 500000000000) (92134617873 / 62500000000) x280 := by
    apply bounds_inv hx279 <;> norm_num
  let x281 : ℝ := x278*x280
  have hx281 : Bounds (57740183757 / 50000000000) (1160608725193 / 1000000000000) x281 := by
    apply bounds_mul hx278 hx280 <;> norm_num
  let x282 : ℝ := x278/x279
  have hx282 : Bounds (57740183757 / 50000000000) (1160608725193 / 1000000000000) x282 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx281
  let x283 : ℝ := -x282
  have hx283 : Bounds (-1160608725193 / 1000000000000) (-57740183757 / 50000000000) x283 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx282
  let x284 : ℝ := x277+x283
  have hx284 : Bounds (-38406677523 / 1000000000000) (-13709119873 / 500000000000) x284 := by
    apply bounds_add hx277 hx283 <;> norm_num
  let x285 : ℝ := x277-x282
  have hx285 : Bounds (-38406677523 / 1000000000000) (-13709119873 / 500000000000) x285 := by
    exact hx284
  let x286 : ℝ := x241*x285
  have hx286 : Bounds (-83493545497 / 1000000000000) (-59362161627 / 1000000000000) x286 := by
    apply bounds_mul hx241 hx285 <;> norm_num
  let x287 : ℝ := x273+x286
  have hx287 : Bounds (-45692566457 / 50000000000) (-875573498873 / 1000000000000) x287 := by
    apply bounds_add hx273 hx286 <;> norm_num
  let x288 : ℝ := (2 / 1)*x192
  have hx288 : Bounds (728530691 / 500000000) (728826513 / 500000000) x288 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x289 : ℝ := c*(1 / 1)
  have hx289 : Bounds (261383 / 1000000) (52487 / 200000) x289 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x290 : ℝ := c*x289
  have hx290 : Bounds (68321072689 / 1000000000000) (2754885169 / 40000000000) x290 := by
    apply bounds_mul hc hx289 <;> norm_num
  let x291 : ℝ := c^2
  have hx291 : Bounds (68321072689 / 1000000000000) (2754885169 / 40000000000) x291 := by
    (convert hx290 using 1; ring)
  let x292 : ℝ := -x291
  have hx292 : Bounds (-2754885169 / 40000000000) (-68321072689 / 1000000000000) x292 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx291
  let x293 : ℝ := x288+x292
  have hx293 : Bounds (55527570111 / 40000000000) (1389331953311 / 1000000000000) x293 := by
    apply bounds_add hx288 hx292 <;> norm_num
  let x294 : ℝ := x288-x291
  have hx294 : Bounds (55527570111 / 40000000000) (1389331953311 / 1000000000000) x294 := by
    exact hx293
  let x295 : ℝ := c*x294
  have hx295 : Bounds (181424535729 / 500000000000) (11394041599 / 31250000000) x295 := by
    apply bounds_mul hc hx294 <;> norm_num
  let x296 : ℝ := x198*(1 / 1)
  have hx296 : Bounds (37245114831 / 40000000000) (931678927311 / 1000000000000) x296 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x297 : ℝ := x198*x296
  have hx297 : Bounds (866999111733 / 1000000000000) (217006405899 / 250000000000) x297 := by
    apply bounds_mul hx198 hx296 <;> norm_num
  let x298 : ℝ := x198^2
  have hx298 : Bounds (866999111733 / 1000000000000) (217006405899 / 250000000000) x298 := by
    (convert hx297 using 1; ring)
  let x299 : ℝ := x192*(1 / 1)
  have hx299 : Bounds (728530691 / 1000000000) (728826513 / 1000000000) x299 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x300 : ℝ := x192*x299
  have hx300 : Bounds (33172310483 / 62500000000) (132797021513 / 250000000000) x300 := by
    apply bounds_mul hx192 hx299 <;> norm_num
  let x301 : ℝ := x192^2
  have hx301 : Bounds (33172310483 / 62500000000) (132797021513 / 250000000000) x301 := by
    (convert hx300 using 1; ring)
  let x302 : ℝ := x298*x301
  have hx302 : Bounds (230082909783 / 500000000000) (461084869643 / 1000000000000) x302 := by
    apply bounds_mul hx298 hx301 <;> norm_num
  let x303 : ℝ := x302⁻¹
  have hx303 : Bounds (1084399061689 / 500000000000) (1086564839761 / 500000000000) x303 := by
    apply bounds_inv hx302 <;> norm_num
  let x304 : ℝ := x295*x303
  have hx304 : Bounds (786946385247 / 1000000000000) (49521459937 / 62500000000) x304 := by
    apply bounds_mul hx295 hx303 <;> norm_num
  let x305 : ℝ := x295/x302
  have hx305 : Bounds (786946385247 / 1000000000000) (49521459937 / 62500000000) x305 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx304
  let x306 : ℝ := c*x220
  have hx306 : Bounds (8951938069 / 62500000000) (36039289541 / 250000000000) x306 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x307 : ℝ := x180+x306
  have hx307 : Bounds (801535534047 / 1000000000000) (401371892857 / 500000000000) x307 := by
    apply bounds_add hx180 hx306 <;> norm_num
  let x308 : ℝ := x307*(1 / 1)
  have hx308 : Bounds (801535534047 / 1000000000000) (401371892857 / 500000000000) x308 := by
    apply bounds_mul hx307 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x309 : ℝ := x307*x308
  have hx309 : Bounds (32122960617 / 50000000000) (644397585503 / 1000000000000) x309 := by
    apply bounds_mul hx307 hx308 <;> norm_num
  let x310 : ℝ := x307^2
  have hx310 : Bounds (32122960617 / 50000000000) (644397585503 / 1000000000000) x310 := by
    (convert hx309 using 1; ring)
  let x311 : ℝ := x287*x310
  have hx311 : Bounds (-588883590007 / 1000000000000) (-562520260431 / 1000000000000) x311 := by
    apply bounds_mul hx287 hx310 <;> norm_num
  let x312 : ℝ := (2 / 1)*x241
  have hx312 : Bounds (2165061002381 / 500000000000) (271741630887 / 62500000000) x312 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx241 <;> norm_num
  let x313 : ℝ := c*x220
  have hx313 : Bounds (8951938069 / 62500000000) (36039289541 / 250000000000) x313 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x314 : ℝ := x180+x313
  have hx314 : Bounds (801535534047 / 1000000000000) (401371892857 / 500000000000) x314 := by
    apply bounds_add hx180 hx313 <;> norm_num
  let x315 : ℝ := x312*x314
  have hx315 : Bounds (138829866143 / 40000000000) (349022248823 / 100000000000) x315 := by
    apply bounds_mul hx312 hx314 <;> norm_num
  let x316 : ℝ := -x209
  have hx316 : Bounds (-107488691 / 400000000) (-267592249 / 1000000000) x316 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x317 : ℝ := x220+x316
  have hx317 : Bounds (558503941 / 2000000000) (35214237 / 125000000) x317 := by
    apply bounds_add hx220 hx316 <;> norm_num
  let x318 : ℝ := x220-x209
  have hx318 : Bounds (558503941 / 2000000000) (35214237 / 125000000) x318 := by
    exact hx317
  let x319 : ℝ := x315*x318
  have hx319 : Bounds (969212842117 / 1000000000000) (983244175067 / 1000000000000) x319 := by
    apply bounds_mul hx315 hx318 <;> norm_num
  let x320 : ℝ := x311+x319
  have hx320 : Bounds (38032925211 / 100000000000) (105180978659 / 250000000000) x320 := by
    apply bounds_add hx311 hx319 <;> norm_num
  let x321 : ℝ := a*(1 / 1)
  have hx321 : Bounds (499 / 1000) (1 / 2) x321 := by
    apply bounds_mul ha (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x322 : ℝ := a*x321
  have hx322 : Bounds (249001 / 1000000) (1 / 4) x322 := by
    apply bounds_mul ha hx321 <;> norm_num
  let x323 : ℝ := a^2
  have hx323 : Bounds (249001 / 1000000) (1 / 4) x323 := by
    (convert hx322 using 1; ring)
  let x324 : ℝ := -x323
  have hx324 : Bounds (-1 / 4) (-249001 / 1000000) x324 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx323
  let x325 : ℝ := (1 / 1)+x324
  have hx325 : Bounds (3 / 4) (750999 / 1000000) x325 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx324 <;> norm_num
  let x326 : ℝ := (1 / 1)-x323
  have hx326 : Bounds (3 / 4) (750999 / 1000000) x326 := by
    exact hx325
  let x327 : ℝ := x326⁻¹
  have hx327 : Bounds (665779847909 / 500000000000) (666666666667 / 500000000000) x327 := by
    apply bounds_inv hx326 <;> norm_num
  let x328 : ℝ := (1 / 1)*x327
  have hx328 : Bounds (665779847909 / 500000000000) (666666666667 / 500000000000) x328 := by
    apply bounds_mul (bounds_const ((1 / 1) : ℝ)) hx327 <;> norm_num
  let x329 : ℝ := (1 / 1)/x326
  have hx329 : Bounds (665779847909 / 500000000000) (666666666667 / 500000000000) x329 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx328
  let x330 : ℝ := x329*x305
  have hx330 : Bounds (261966522341 / 250000000000) (105645781199 / 100000000000) x330 := by
    apply bounds_mul hx329 hx305 <;> norm_num
  let x331 : ℝ := x320+x330
  have hx331 : Bounds (714097670737 / 500000000000) (738590863313 / 500000000000) x331 := by
    apply bounds_add hx320 hx330 <;> norm_num
  let x332 : ℝ := x180*(1 / 1)
  have hx332 : Bounds (658304524943 / 1000000000000) (13171732551 / 20000000000) x332 := by
    apply bounds_mul hx180 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x333 : ℝ := x180*x332
  have hx333 : Bounds (10834121189 / 25000000000) (108434086497 / 250000000000) x333 := by
    apply bounds_mul hx180 hx332 <;> norm_num
  let x334 : ℝ := x180^2
  have hx334 : Bounds (10834121189 / 25000000000) (108434086497 / 250000000000) x334 := by
    (convert hx333 using 1; ring)
  let x335 : ℝ := x331*x334
  have hx335 : Bounds (618929656443 / 1000000000000) (160176851117 / 250000000000) x335 := by
    apply bounds_mul hx331 hx334 <;> norm_num
  let x336 : ℝ := x90*x192
  have hx336 : Bounds (457328656531 / 1000000000000) (457714334567 / 1000000000000) x336 := by
    apply bounds_mul hx90 hx192 <;> norm_num
  let x337 : ℝ := x336⁻¹
  have hx337 : Bounds (2184768805517 / 1000000000000) (273326410263 / 125000000000) x337 := by
    apply bounds_inv hx336 <;> norm_num
  let x338 : ℝ := x335*x337
  have hx338 : Bounds (676109103103 / 500000000000) (700489019569 / 500000000000) x338 := by
    apply bounds_mul hx335 hx337 <;> norm_num
  let x339 : ℝ := x335/x336
  have hx339 : Bounds (676109103103 / 500000000000) (700489019569 / 500000000000) x339 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx338
  have hu : x339 < (894075455392128665381569 / 563999498001000000000000) := lt_of_le_of_lt hx339.2 (by norm_num)
  simpa +zetaDelta only [ScFormula,Kprime,K,Mprime,SmallMean.A,biasB,div_one,pow_two] using hu

open GeneralCK.Reflection
/-- Uniform derivative enclosure including input boxes with z=0. -/
theorem derivative_bound_899 {a z s : ℝ}
    (ha : a ∈ Set.Icc ((499 / 1000):ℝ) ((1 / 2)))
    (hz : z ∈ Set.Icc (0:ℝ) (1/1000))
    (hs : s ∈ Set.Ioo (a*(1-z)/2) (a*(1+z)/2)) :
    P a ((biasE a+biasE (a*z))/2) s ≤ (894075455392128665381569 / 563999498001000000000000) := by
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
  have hsl : (498501 / 2000000) ≤ s := by
    have h := mul_le_mul ha.1 (show (999/1000:ℝ) ≤ 1-z by linarith [hz.2])
      (by norm_num : (0:ℝ) ≤ 999/1000) ha0.le
    nlinarith [hs.1]
  have hsu : s ≤ (1001 / 4000) := by
    have h := mul_le_mul ha.2 (show 1+z ≤ (1001/1000:ℝ) by linarith [hz.2])
      (by linarith [hz.1] : 0 ≤ 1+z) (by norm_num : (0:ℝ) ≤ (1 / 2))
    nlinarith [hs.2]
  have hy := div_pos he hs0
  have hc := biasContact_mem hy
  have heq : biasE (biasContact (((biasE a+biasE (a*z))/2)/s)) =
      (((biasE a+biasE (a*z))/2)/s)*biasContact (((biasE a+biasE (a*z))/2)/s) := by
    exact (div_eq_iff hc.1.ne').mp (biasR_biasContact hy)
  have hb := derivative_leaf_899 a z s _ ha hz ⟨hsl,hsu⟩ hc.1.le hc.2.le heq
  rw [P_eq_formula ha0 ha1 he hs0]
  exact hb.le

/-- Checked low-ratio strip: includes arbitrarily small positive z. -/
theorem curvature_leaf_899 {a z : ℝ}
    (ha : a ∈ Set.Icc ((499 / 1000):ℝ) ((1 / 2)))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < curvature a (a*z) := by
  have ha0 : 0 < a := by linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  apply curvature_pos_of_derivative_bound ha0 ha1 hz.1 (by linarith [hz.2])
    (fun s hs => derivative_bound_899 ha ⟨hz.1.le,hz.2⟩ hs) (M := (894075455392128665381569 / 563999498001000000000000))
  exact lt_of_lt_of_le (by norm_num : (894075455392128665381569 / 563999498001000000000000) < 2*((499 / 1000):ℝ)/(1-((499 / 1000):ℝ)^2)^2)
    (base_mono (by norm_num) ha.1 ha1)

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Cell0900 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
theorem derivative_leaf_900 (a z s c : ℝ)
    (ha : Bounds (1 / 2) (503 / 1000) a) (hz : Bounds 0 (1/1000) z)
    (hs : Bounds (999 / 4000) (503503 / 2000000) s) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (heq : biasE c = (((biasE a+biasE (a*z))/2)/s)*c) :
    ScFormula c a ((biasE a+biasE (a*z))/2)*(biasE c)^2 /
      (((biasE a+biasE (a*z))/2)*biasB c) < (5794535752043 / 3600000000000) := by
  let x0 : ℝ := Real.log (2 / 1)
  have hx0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x0 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x1 : ℝ := (1 / 1)+(503 / 1000)
  have hx1 : Bounds (1503 / 1000) (1503 / 1000) x1 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((503 / 1000) : ℝ)) <;> norm_num
  let x2 : ℝ := (1 / 1)+(503 / 1000)
  have hx2 : Bounds (1503 / 1000) (1503 / 1000) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((503 / 1000) : ℝ)) <;> norm_num
  let x3 : ℝ := Real.log x2
  have hx3 : Bounds (40746311 / 100000000) (407463111 / 1000000000) x3 := by
    exact bounds_log hx2 (by norm_num) (by simpa only [div_one] using reflection_log_12553.1) (by simpa only [div_one] using reflection_log_12553.2)
  let x4 : ℝ := x1*x3
  have hx4 : Bounds (61241705433 / 100000000000) (612417055833 / 1000000000000) x4 := by
    apply bounds_mul hx1 hx3 <;> norm_num
  let x5 : ℝ := -(503 / 1000)
  have hx5 : Bounds (-503 / 1000) (-503 / 1000) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((503 / 1000) : ℝ))
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (497 / 1000) (497 / 1000) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-(503 / 1000)
  have hx7 : Bounds (497 / 1000) (497 / 1000) x7 := by
    exact hx6
  let x8 : ℝ := -(503 / 1000)
  have hx8 : Bounds (-503 / 1000) (-503 / 1000) x8 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((503 / 1000) : ℝ))
  let x9 : ℝ := (1 / 1)+x8
  have hx9 : Bounds (497 / 1000) (497 / 1000) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx8 <;> norm_num
  let x10 : ℝ := (1 / 1)-(503 / 1000)
  have hx10 : Bounds (497 / 1000) (497 / 1000) x10 := by
    exact hx9
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (-349582627 / 500000000) (-174791313 / 250000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_12554.1) (by simpa only [div_one] using reflection_log_12554.2)
  let x12 : ℝ := x7*x11
  have hx12 : Bounds (-173742565619 / 500000000000) (-86871282561 / 250000000000) x12 := by
    apply bounds_mul hx7 hx11 <;> norm_num
  let x13 : ℝ := x4+x12
  have hx13 : Bounds (66232980773 / 250000000000) (264931925589 / 1000000000000) x13 := by
    apply bounds_add hx4 hx12 <;> norm_num
  let x14 : ℝ := (2 / 1)⁻¹
  have hx14 : Bounds (1 / 2) (1 / 2) x14 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x15 : ℝ := x13*x14
  have hx15 : Bounds (66232980773 / 500000000000) (26493192559 / 200000000000) x15 := by
    apply bounds_mul hx13 hx14 <;> norm_num
  let x16 : ℝ := x13/(2 / 1)
  have hx16 : Bounds (66232980773 / 500000000000) (26493192559 / 200000000000) x16 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx15
  let x17 : ℝ := -x16
  have hx17 : Bounds (-26493192559 / 200000000000) (-66232980773 / 500000000000) x17 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx16
  let x18 : ℝ := x0+x17
  have hx18 : Bounds (112136243441 / 200000000000) (280340609727 / 500000000000) x18 := by
    apply bounds_add hx0 hx17 <;> norm_num
  let x19 : ℝ := x0-x16
  have hx19 : Bounds (112136243441 / 200000000000) (280340609727 / 500000000000) x19 := by
    exact hx18
  let x20 : ℝ := biasE (503 / 1000)
  have hx20 : Bounds (112136243441 / 200000000000) (280340609727 / 500000000000) x20 := by
    simpa +zetaDelta only [biasE, div_one] using hx19
  let x21 : ℝ := Real.log (2 / 1)
  have hx21 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x21 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x22 : ℝ := (1 / 1)+(1 / 2)
  have hx22 : Bounds (3 / 2) (3 / 2) x22 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1 / 2) : ℝ)) <;> norm_num
  let x23 : ℝ := (1 / 1)+(1 / 2)
  have hx23 : Bounds (3 / 2) (3 / 2) x23 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1 / 2) : ℝ)) <;> norm_num
  let x24 : ℝ := Real.log x23
  have hx24 : Bounds (101366277 / 250000000) (405465109 / 1000000000) x24 := by
    exact bounds_log hx23 (by norm_num) (by simpa only [div_one] using reflection_log_6969.1) (by simpa only [div_one] using reflection_log_6969.2)
  let x25 : ℝ := x22*x24
  have hx25 : Bounds (304098831 / 500000000) (1216395327 / 2000000000) x25 := by
    apply bounds_mul hx22 hx24 <;> norm_num
  let x26 : ℝ := -(1 / 2)
  have hx26 : Bounds (-1 / 2) (-1 / 2) x26 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1 / 2) : ℝ))
  let x27 : ℝ := (1 / 1)+x26
  have hx27 : Bounds (1 / 2) (1 / 2) x27 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx26 <;> norm_num
  let x28 : ℝ := (1 / 1)-(1 / 2)
  have hx28 : Bounds (1 / 2) (1 / 2) x28 := by
    exact hx27
  let x29 : ℝ := -(1 / 2)
  have hx29 : Bounds (-1 / 2) (-1 / 2) x29 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1 / 2) : ℝ))
  let x30 : ℝ := (1 / 1)+x29
  have hx30 : Bounds (1 / 2) (1 / 2) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx29 <;> norm_num
  let x31 : ℝ := (1 / 1)-(1 / 2)
  have hx31 : Bounds (1 / 2) (1 / 2) x31 := by
    exact hx30
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (-693147181 / 1000000000) (-34657359 / 50000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_12540.1) (by simpa only [div_one] using reflection_log_12540.2)
  let x33 : ℝ := x28*x32
  have hx33 : Bounds (-693147181 / 2000000000) (-34657359 / 100000000) x33 := by
    apply bounds_mul hx28 hx32 <;> norm_num
  let x34 : ℝ := x25+x33
  have hx34 : Bounds (523248143 / 2000000000) (523248147 / 2000000000) x34 := by
    apply bounds_add hx25 hx33 <;> norm_num
  let x35 : ℝ := (2 / 1)⁻¹
  have hx35 : Bounds (1 / 2) (1 / 2) x35 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x36 : ℝ := x34*x35
  have hx36 : Bounds (523248143 / 4000000000) (523248147 / 4000000000) x36 := by
    apply bounds_mul hx34 hx35 <;> norm_num
  let x37 : ℝ := x34/(2 / 1)
  have hx37 : Bounds (523248143 / 4000000000) (523248147 / 4000000000) x37 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx36
  let x38 : ℝ := -x37
  have hx38 : Bounds (-523248147 / 4000000000) (-523248143 / 4000000000) x38 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx37
  let x39 : ℝ := x21+x38
  have hx39 : Bounds (2249340573 / 4000000000) (2249340581 / 4000000000) x39 := by
    apply bounds_add hx21 hx38 <;> norm_num
  let x40 : ℝ := x21-x37
  have hx40 : Bounds (2249340573 / 4000000000) (2249340581 / 4000000000) x40 := by
    exact hx39
  let x41 : ℝ := biasE (1 / 2)
  have hx41 : Bounds (2249340573 / 4000000000) (2249340581 / 4000000000) x41 := by
    simpa +zetaDelta only [biasE, div_one] using hx40
  let x42 : ℝ := biasE a
  have hx42 : Bounds (112136243441 / 200000000000) (2249340581 / 4000000000) x42 := by
    exact bounds_biasE ha (by norm_num) (by norm_num) hx20.1 hx41.2
  let x43 : ℝ := a*z
  have hx43 : Bounds (0 / 1) (503 / 1000000) x43 := by
    apply bounds_mul ha hz <;> norm_num
  let x44 : ℝ := Real.log (2 / 1)
  have hx44 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x44 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x45 : ℝ := (1 / 1)+(503 / 1000000)
  have hx45 : Bounds (1000503 / 1000000) (1000503 / 1000000) x45 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((503 / 1000000) : ℝ)) <;> norm_num
  let x46 : ℝ := (1 / 1)+(503 / 1000000)
  have hx46 : Bounds (1000503 / 1000000) (1000503 / 1000000) x46 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((503 / 1000000) : ℝ)) <;> norm_num
  let x47 : ℝ := Real.log x46
  have hx47 : Bounds (502873 / 1000000000) (251437 / 500000000) x47 := by
    exact bounds_log hx46 (by norm_num) (by simpa only [div_one] using reflection_log_12555.1) (by simpa only [div_one] using reflection_log_12555.2)
  let x48 : ℝ := x45*x47
  have hx48 : Bounds (100625189 / 200000000000) (251563473 / 500000000000) x48 := by
    apply bounds_mul hx45 hx47 <;> norm_num
  let x49 : ℝ := -(503 / 1000000)
  have hx49 : Bounds (-503 / 1000000) (-503 / 1000000) x49 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((503 / 1000000) : ℝ))
  let x50 : ℝ := (1 / 1)+x49
  have hx50 : Bounds (999497 / 1000000) (999497 / 1000000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx49 <;> norm_num
  let x51 : ℝ := (1 / 1)-(503 / 1000000)
  have hx51 : Bounds (999497 / 1000000) (999497 / 1000000) x51 := by
    exact hx50
  let x52 : ℝ := -(503 / 1000000)
  have hx52 : Bounds (-503 / 1000000) (-503 / 1000000) x52 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((503 / 1000000) : ℝ))
  let x53 : ℝ := (1 / 1)+x52
  have hx53 : Bounds (999497 / 1000000) (999497 / 1000000) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx52 <;> norm_num
  let x54 : ℝ := (1 / 1)-(503 / 1000000)
  have hx54 : Bounds (999497 / 1000000) (999497 / 1000000) x54 := by
    exact hx53
  let x55 : ℝ := Real.log x54
  have hx55 : Bounds (-503127 / 1000000000) (-251563 / 500000000) x55 := by
    exact bounds_log hx54 (by norm_num) (by simpa only [div_one] using reflection_log_12556.1) (by simpa only [div_one] using reflection_log_12556.2)
  let x56 : ℝ := x51*x55
  have hx56 : Bounds (-62859241 / 125000000000) (-502872927 / 1000000000000) x56 := by
    apply bounds_mul hx51 hx55 <;> norm_num
  let x57 : ℝ := x48+x56
  have hx57 : Bounds (252017 / 1000000000000) (254019 / 1000000000000) x57 := by
    apply bounds_add hx48 hx56 <;> norm_num
  let x58 : ℝ := (2 / 1)⁻¹
  have hx58 : Bounds (1 / 2) (1 / 2) x58 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x59 : ℝ := x57*x58
  have hx59 : Bounds (15751 / 125000000000) (12701 / 100000000000) x59 := by
    apply bounds_mul hx57 hx58 <;> norm_num
  let x60 : ℝ := x57/(2 / 1)
  have hx60 : Bounds (15751 / 125000000000) (12701 / 100000000000) x60 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx59
  let x61 : ℝ := -x60
  have hx61 : Bounds (-12701 / 100000000000) (-15751 / 125000000000) x61 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx60
  let x62 : ℝ := x44+x61
  have hx62 : Bounds (69314705299 / 100000000000) (43321690937 / 62500000000) x62 := by
    apply bounds_add hx44 hx61 <;> norm_num
  let x63 : ℝ := x44-x60
  have hx63 : Bounds (69314705299 / 100000000000) (43321690937 / 62500000000) x63 := by
    exact hx62
  let x64 : ℝ := biasE (503 / 1000000)
  have hx64 : Bounds (69314705299 / 100000000000) (43321690937 / 62500000000) x64 := by
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
  have hx86 : Bounds (69314705299 / 100000000000) (693147181 / 1000000000) x86 := by
    exact bounds_biasE hx43 (by norm_num) (by norm_num) hx64.1 hx85.2
  let x87 : ℝ := x42+x86
  have hx87 : Bounds (250765654039 / 200000000000) (1004385861 / 800000000) x87 := by
    apply bounds_add hx42 hx86 <;> norm_num
  let x88 : ℝ := (2 / 1)⁻¹
  have hx88 : Bounds (1 / 2) (1 / 2) x88 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x89 : ℝ := x87*x88
  have hx89 : Bounds (626914135097 / 1000000000000) (1004385861 / 1600000000) x89 := by
    apply bounds_mul hx87 hx88 <;> norm_num
  let x90 : ℝ := x87/(2 / 1)
  have hx90 : Bounds (626914135097 / 1000000000000) (1004385861 / 1600000000) x90 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx89
  let x91 : ℝ := s⁻¹
  have hx91 : Bounds (1986085485091 / 500000000000) (800800800801 / 200000000000) x91 := by
    apply bounds_inv hs <;> norm_num
  let x92 : ℝ := x90*x91
  have hx92 : Bounds (2490210128229 / 1000000000000) (314184766329 / 125000000000) x92 := by
    apply bounds_mul hx90 hx91 <;> norm_num
  let x93 : ℝ := x90/s
  have hx93 : Bounds (2490210128229 / 1000000000000) (314184766329 / 125000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(6549 / 25000)
  have hx95 : Bounds (31549 / 25000) (31549 / 25000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((6549 / 25000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(6549 / 25000)
  have hx96 : Bounds (31549 / 25000) (31549 / 25000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((6549 / 25000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (232666067 / 1000000000) (58166517 / 250000000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_12557.1) (by simpa only [div_one] using reflection_log_12557.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (293615269911 / 1000000000000) (146807635587 / 500000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(6549 / 25000)
  have hx99 : Bounds (-6549 / 25000) (-6549 / 25000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((6549 / 25000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (18451 / 25000) (18451 / 25000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(6549 / 25000)
  have hx101 : Bounds (18451 / 25000) (18451 / 25000) x101 := by
    exact hx100
  let x102 : ℝ := -(6549 / 25000)
  have hx102 : Bounds (-6549 / 25000) (-6549 / 25000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((6549 / 25000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (18451 / 25000) (18451 / 25000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(6549 / 25000)
  have hx104 : Bounds (18451 / 25000) (18451 / 25000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-37969657 / 125000000) (-60751451 / 200000000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_12558.1) (by simpa only [div_one] using reflection_log_12558.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-224185005219 / 1000000000000) (-700578139 / 3125000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (17357566173 / 250000000000) (34715133347 / 500000000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (17357566173 / 500000000000) (34715133347 / 1000000000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (17357566173 / 500000000000) (34715133347 / 1000000000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-34715133347 / 1000000000000) (-17357566173 / 500000000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (658432046653 / 1000000000000) (329216024327 / 500000000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (658432046653 / 1000000000000) (329216024327 / 500000000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (6549 / 25000)
  have hx114 : Bounds (658432046653 / 1000000000000) (329216024327 / 500000000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(26417 / 100000)
  have hx116 : Bounds (126417 / 100000) (126417 / 100000) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((26417 / 100000) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(26417 / 100000)
  have hx117 : Bounds (126417 / 100000) (126417 / 100000) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((26417 / 100000) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (11720789 / 50000000) (234415781 / 1000000000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_12559.1) (by simpa only [div_one] using reflection_log_12559.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (148170698301 / 500000000000) (296341397867 / 1000000000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(26417 / 100000)
  have hx120 : Bounds (-26417 / 100000) (-26417 / 100000) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((26417 / 100000) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (73583 / 100000) (73583 / 100000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(26417 / 100000)
  have hx122 : Bounds (73583 / 100000) (73583 / 100000) x122 := by
    exact hx121
  let x123 : ℝ := -(26417 / 100000)
  have hx123 : Bounds (-26417 / 100000) (-26417 / 100000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((26417 / 100000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (73583 / 100000) (73583 / 100000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(26417 / 100000)
  have hx125 : Bounds (73583 / 100000) (73583 / 100000) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-153378083 / 500000000) (-61351233 / 200000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_12560.1) (by simpa only [div_one] using reflection_log_12560.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-56430097407 / 250000000000) (-225720388891 / 1000000000000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (35310503487 / 500000000000) (4413813061 / 62500000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (35310503487 / 1000000000000) (4413813061 / 125000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (35310503487 / 1000000000000) (4413813061 / 125000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-4413813061 / 125000000000) (-35310503487 / 1000000000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (82229584439 / 125000000000) (657836677513 / 1000000000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (82229584439 / 125000000000) (657836677513 / 1000000000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (26417 / 100000)
  have hx135 : Bounds (82229584439 / 125000000000) (657836677513 / 1000000000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(6549 / 25000)
  have hx136 : Bounds (65233544519 / 100000000000) (658430731101 / 1000000000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((6549 / 25000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(26417 / 100000)
  have hx137 : Bounds (328919404787 / 500000000000) (66398551777 / 100000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((26417 / 100000) : ℝ)) <;> norm_num
  have hc : Bounds (6549 / 25000) (26417 / 100000) c := by
    apply contact_bracket hc0 hc1 (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x93 by linarith [hx93.1])
      (show biasE c = x93*c by simpa +zetaDelta only [div_one] using heq)
    · have h1 : x93*(6549 / 25000) ≤ (658430731101 / 1000000000000) := hx136.2
      have h2 : (658432046653 / 1000000000000) ≤ biasE (6549 / 25000) := hx114.1
      linarith
    · have h1 : biasE (26417 / 100000) ≤ (657836677513 / 1000000000000) := hx135.2
      have h2 : (328919404787 / 500000000000) ≤ x93*(26417 / 100000) := hx137.1
      linarith
  let x138 : ℝ := Real.log (2 / 1)
  have hx138 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x138 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x139 : ℝ := (1 / 1)+(26417 / 100000)
  have hx139 : Bounds (126417 / 100000) (126417 / 100000) x139 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((26417 / 100000) : ℝ)) <;> norm_num
  let x140 : ℝ := (1 / 1)+(26417 / 100000)
  have hx140 : Bounds (126417 / 100000) (126417 / 100000) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((26417 / 100000) : ℝ)) <;> norm_num
  let x141 : ℝ := Real.log x140
  have hx141 : Bounds (11720789 / 50000000) (234415781 / 1000000000) x141 := by
    exact bounds_log hx140 (by norm_num) (by simpa only [div_one] using reflection_log_12559.1) (by simpa only [div_one] using reflection_log_12559.2)
  let x142 : ℝ := x139*x141
  have hx142 : Bounds (148170698301 / 500000000000) (296341397867 / 1000000000000) x142 := by
    apply bounds_mul hx139 hx141 <;> norm_num
  let x143 : ℝ := -(26417 / 100000)
  have hx143 : Bounds (-26417 / 100000) (-26417 / 100000) x143 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((26417 / 100000) : ℝ))
  let x144 : ℝ := (1 / 1)+x143
  have hx144 : Bounds (73583 / 100000) (73583 / 100000) x144 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx143 <;> norm_num
  let x145 : ℝ := (1 / 1)-(26417 / 100000)
  have hx145 : Bounds (73583 / 100000) (73583 / 100000) x145 := by
    exact hx144
  let x146 : ℝ := -(26417 / 100000)
  have hx146 : Bounds (-26417 / 100000) (-26417 / 100000) x146 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((26417 / 100000) : ℝ))
  let x147 : ℝ := (1 / 1)+x146
  have hx147 : Bounds (73583 / 100000) (73583 / 100000) x147 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx146 <;> norm_num
  let x148 : ℝ := (1 / 1)-(26417 / 100000)
  have hx148 : Bounds (73583 / 100000) (73583 / 100000) x148 := by
    exact hx147
  let x149 : ℝ := Real.log x148
  have hx149 : Bounds (-153378083 / 500000000) (-61351233 / 200000000) x149 := by
    exact bounds_log hx148 (by norm_num) (by simpa only [div_one] using reflection_log_12560.1) (by simpa only [div_one] using reflection_log_12560.2)
  let x150 : ℝ := x145*x149
  have hx150 : Bounds (-56430097407 / 250000000000) (-225720388891 / 1000000000000) x150 := by
    apply bounds_mul hx145 hx149 <;> norm_num
  let x151 : ℝ := x142+x150
  have hx151 : Bounds (35310503487 / 500000000000) (4413813061 / 62500000000) x151 := by
    apply bounds_add hx142 hx150 <;> norm_num
  let x152 : ℝ := (2 / 1)⁻¹
  have hx152 : Bounds (1 / 2) (1 / 2) x152 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x153 : ℝ := x151*x152
  have hx153 : Bounds (35310503487 / 1000000000000) (4413813061 / 125000000000) x153 := by
    apply bounds_mul hx151 hx152 <;> norm_num
  let x154 : ℝ := x151/(2 / 1)
  have hx154 : Bounds (35310503487 / 1000000000000) (4413813061 / 125000000000) x154 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx153
  let x155 : ℝ := -x154
  have hx155 : Bounds (-4413813061 / 125000000000) (-35310503487 / 1000000000000) x155 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx154
  let x156 : ℝ := x138+x155
  have hx156 : Bounds (82229584439 / 125000000000) (657836677513 / 1000000000000) x156 := by
    apply bounds_add hx138 hx155 <;> norm_num
  let x157 : ℝ := x138-x154
  have hx157 : Bounds (82229584439 / 125000000000) (657836677513 / 1000000000000) x157 := by
    exact hx156
  let x158 : ℝ := biasE (26417 / 100000)
  have hx158 : Bounds (82229584439 / 125000000000) (657836677513 / 1000000000000) x158 := by
    simpa +zetaDelta only [biasE, div_one] using hx157
  let x159 : ℝ := Real.log (2 / 1)
  have hx159 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x159 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x160 : ℝ := (1 / 1)+(6549 / 25000)
  have hx160 : Bounds (31549 / 25000) (31549 / 25000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((6549 / 25000) : ℝ)) <;> norm_num
  let x161 : ℝ := (1 / 1)+(6549 / 25000)
  have hx161 : Bounds (31549 / 25000) (31549 / 25000) x161 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((6549 / 25000) : ℝ)) <;> norm_num
  let x162 : ℝ := Real.log x161
  have hx162 : Bounds (232666067 / 1000000000) (58166517 / 250000000) x162 := by
    exact bounds_log hx161 (by norm_num) (by simpa only [div_one] using reflection_log_12557.1) (by simpa only [div_one] using reflection_log_12557.2)
  let x163 : ℝ := x160*x162
  have hx163 : Bounds (293615269911 / 1000000000000) (146807635587 / 500000000000) x163 := by
    apply bounds_mul hx160 hx162 <;> norm_num
  let x164 : ℝ := -(6549 / 25000)
  have hx164 : Bounds (-6549 / 25000) (-6549 / 25000) x164 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((6549 / 25000) : ℝ))
  let x165 : ℝ := (1 / 1)+x164
  have hx165 : Bounds (18451 / 25000) (18451 / 25000) x165 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx164 <;> norm_num
  let x166 : ℝ := (1 / 1)-(6549 / 25000)
  have hx166 : Bounds (18451 / 25000) (18451 / 25000) x166 := by
    exact hx165
  let x167 : ℝ := -(6549 / 25000)
  have hx167 : Bounds (-6549 / 25000) (-6549 / 25000) x167 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((6549 / 25000) : ℝ))
  let x168 : ℝ := (1 / 1)+x167
  have hx168 : Bounds (18451 / 25000) (18451 / 25000) x168 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx167 <;> norm_num
  let x169 : ℝ := (1 / 1)-(6549 / 25000)
  have hx169 : Bounds (18451 / 25000) (18451 / 25000) x169 := by
    exact hx168
  let x170 : ℝ := Real.log x169
  have hx170 : Bounds (-37969657 / 125000000) (-60751451 / 200000000) x170 := by
    exact bounds_log hx169 (by norm_num) (by simpa only [div_one] using reflection_log_12558.1) (by simpa only [div_one] using reflection_log_12558.2)
  let x171 : ℝ := x166*x170
  have hx171 : Bounds (-224185005219 / 1000000000000) (-700578139 / 3125000000) x171 := by
    apply bounds_mul hx166 hx170 <;> norm_num
  let x172 : ℝ := x163+x171
  have hx172 : Bounds (17357566173 / 250000000000) (34715133347 / 500000000000) x172 := by
    apply bounds_add hx163 hx171 <;> norm_num
  let x173 : ℝ := (2 / 1)⁻¹
  have hx173 : Bounds (1 / 2) (1 / 2) x173 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x174 : ℝ := x172*x173
  have hx174 : Bounds (17357566173 / 500000000000) (34715133347 / 1000000000000) x174 := by
    apply bounds_mul hx172 hx173 <;> norm_num
  let x175 : ℝ := x172/(2 / 1)
  have hx175 : Bounds (17357566173 / 500000000000) (34715133347 / 1000000000000) x175 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx174
  let x176 : ℝ := -x175
  have hx176 : Bounds (-34715133347 / 1000000000000) (-17357566173 / 500000000000) x176 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx175
  let x177 : ℝ := x159+x176
  have hx177 : Bounds (658432046653 / 1000000000000) (329216024327 / 500000000000) x177 := by
    apply bounds_add hx159 hx176 <;> norm_num
  let x178 : ℝ := x159-x175
  have hx178 : Bounds (658432046653 / 1000000000000) (329216024327 / 500000000000) x178 := by
    exact hx177
  let x179 : ℝ := biasE (6549 / 25000)
  have hx179 : Bounds (658432046653 / 1000000000000) (329216024327 / 500000000000) x179 := by
    simpa +zetaDelta only [biasE, div_one] using hx178
  let x180 : ℝ := biasE c
  have hx180 : Bounds (82229584439 / 125000000000) (329216024327 / 500000000000) x180 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx158.1 hx179.2
  let x181 : ℝ := Real.log (2 / 1)
  have hx181 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x181 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x182 : ℝ := c*c
  have hx182 : Bounds (42889401 / 625000000) (697857889 / 10000000000) x182 := by
    apply bounds_mul hc hc <;> norm_num
  let x183 : ℝ := -x182
  have hx183 : Bounds (-697857889 / 10000000000) (-42889401 / 625000000) x183 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx182
  let x184 : ℝ := (1 / 1)+x183
  have hx184 : Bounds (9302142111 / 10000000000) (582110599 / 625000000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx183 <;> norm_num
  let x185 : ℝ := (1 / 1)-x182
  have hx185 : Bounds (9302142111 / 10000000000) (582110599 / 625000000) x185 := by
    exact hx184
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (-14468077 / 200000000) (-71091187 / 1000000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_12561.1) (by simpa only [div_one] using reflection_log_12562.2)
  let x187 : ℝ := (2 / 1)⁻¹
  have hx187 : Bounds (1 / 2) (1 / 2) x187 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x188 : ℝ := x186*x187
  have hx188 : Bounds (-14468077 / 400000000) (-71091187 / 2000000000) x188 := by
    apply bounds_mul hx186 hx187 <;> norm_num
  let x189 : ℝ := x186/(2 / 1)
  have hx189 : Bounds (-14468077 / 400000000) (-71091187 / 2000000000) x189 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx188
  let x190 : ℝ := -x189
  have hx190 : Bounds (71091187 / 2000000000) (14468077 / 400000000) x190 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx189
  let x191 : ℝ := x181+x190
  have hx191 : Bounds (1457385547 / 2000000000) (1458634747 / 2000000000) x191 := by
    apply bounds_add hx181 hx190 <;> norm_num
  let x192 : ℝ := x181-x189
  have hx192 : Bounds (1457385547 / 2000000000) (1458634747 / 2000000000) x192 := by
    exact hx191
  let x193 : ℝ := c*(1 / 1)
  have hx193 : Bounds (6549 / 25000) (26417 / 100000) x193 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x194 : ℝ := c*x193
  have hx194 : Bounds (42889401 / 625000000) (697857889 / 10000000000) x194 := by
    apply bounds_mul hc hx193 <;> norm_num
  let x195 : ℝ := c^2
  have hx195 : Bounds (42889401 / 625000000) (697857889 / 10000000000) x195 := by
    (convert hx194 using 1; ring)
  let x196 : ℝ := -x195
  have hx196 : Bounds (-697857889 / 10000000000) (-42889401 / 625000000) x196 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx195
  let x197 : ℝ := (1 / 1)+x196
  have hx197 : Bounds (9302142111 / 10000000000) (582110599 / 625000000) x197 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx196 <;> norm_num
  let x198 : ℝ := (1 / 1)-x195
  have hx198 : Bounds (9302142111 / 10000000000) (582110599 / 625000000) x198 := by
    exact hx197
  let x199 : ℝ := (1 / 1)+c
  have hx199 : Bounds (31549 / 25000) (126417 / 100000) x199 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x200 : ℝ := -c
  have hx200 : Bounds (-26417 / 100000) (-6549 / 25000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x201 : ℝ := (1 / 1)+x200
  have hx201 : Bounds (73583 / 100000) (18451 / 25000) x201 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx200 <;> norm_num
  let x202 : ℝ := (1 / 1)-c
  have hx202 : Bounds (73583 / 100000) (18451 / 25000) x202 := by
    exact hx201
  let x203 : ℝ := x202⁻¹
  have hx203 : Bounds (1354940111647 / 1000000000000) (679504776919 / 500000000000) x203 := by
    apply bounds_inv hx202 <;> norm_num
  let x204 : ℝ := x199*x203
  have hx204 : Bounds (854940111647 / 500000000000) (429504776919 / 250000000000) x204 := by
    apply bounds_mul hx199 hx203 <;> norm_num
  let x205 : ℝ := x199/x202
  have hx205 : Bounds (854940111647 / 500000000000) (429504776919 / 250000000000) x205 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx204
  let x206 : ℝ := Real.log x205
  have hx206 : Bounds (536423323 / 1000000000) (270585973 / 500000000) x206 := by
    exact bounds_log hx205 (by norm_num) (by simpa only [div_one] using reflection_log_12563.1) (by simpa only [div_one] using reflection_log_12564.2)
  let x207 : ℝ := (2 / 1)⁻¹
  have hx207 : Bounds (1 / 2) (1 / 2) x207 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x208 : ℝ := x206*x207
  have hx208 : Bounds (536423323 / 2000000000) (270585973 / 1000000000) x208 := by
    apply bounds_mul hx206 hx207 <;> norm_num
  let x209 : ℝ := x206/(2 / 1)
  have hx209 : Bounds (536423323 / 2000000000) (270585973 / 1000000000) x209 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx208
  let x210 : ℝ := (1 / 1)+a
  have hx210 : Bounds (3 / 2) (1503 / 1000) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) ha <;> norm_num
  let x211 : ℝ := -a
  have hx211 : Bounds (-503 / 1000) (-1 / 2) x211 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg ha
  let x212 : ℝ := (1 / 1)+x211
  have hx212 : Bounds (497 / 1000) (1 / 2) x212 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx211 <;> norm_num
  let x213 : ℝ := (1 / 1)-a
  have hx213 : Bounds (497 / 1000) (1 / 2) x213 := by
    exact hx212
  let x214 : ℝ := x213⁻¹
  have hx214 : Bounds (2 / 1) (125754527163 / 62500000000) x214 := by
    apply bounds_inv hx213 <;> norm_num
  let x215 : ℝ := x210*x214
  have hx215 : Bounds (3 / 1) (94504527163 / 31250000000) x215 := by
    apply bounds_mul hx210 hx214 <;> norm_num
  let x216 : ℝ := x210/x213
  have hx216 : Bounds (3 / 1) (94504527163 / 31250000000) x216 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx215
  let x217 : ℝ := Real.log x216
  have hx217 : Bounds (17165817 / 15625000) (221325673 / 200000000) x217 := by
    exact bounds_log hx216 (by norm_num) (by simpa only [div_one] using reflection_log_12552.1) (by simpa only [div_one] using reflection_log_12565.2)
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (17165817 / 31250000) (221325673 / 400000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (17165817 / 31250000) (221325673 / 400000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := (2 / 1)*x192
  have hx221 : Bounds (1457385547 / 1000000000) (1458634747 / 1000000000) x221 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x222 : ℝ := c*(1 / 1)
  have hx222 : Bounds (6549 / 25000) (26417 / 100000) x222 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x223 : ℝ := c*x222
  have hx223 : Bounds (42889401 / 625000000) (697857889 / 10000000000) x223 := by
    apply bounds_mul hc hx222 <;> norm_num
  let x224 : ℝ := c^2
  have hx224 : Bounds (42889401 / 625000000) (697857889 / 10000000000) x224 := by
    (convert hx223 using 1; ring)
  let x225 : ℝ := -x224
  have hx225 : Bounds (-697857889 / 10000000000) (-42889401 / 625000000) x225 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx224
  let x226 : ℝ := x221+x225
  have hx226 : Bounds (13875997581 / 10000000000) (6950058527 / 5000000000) x226 := by
    apply bounds_add hx221 hx225 <;> norm_num
  let x227 : ℝ := x221-x224
  have hx227 : Bounds (13875997581 / 10000000000) (6950058527 / 5000000000) x227 := by
    exact hx226
  let x228 : ℝ := x180*x227
  have hx228 : Bounds (912814011809 / 1000000000000) (22880706371 / 25000000000) x228 := by
    apply bounds_mul hx180 hx227 <;> norm_num
  let x229 : ℝ := (2 / 1)*x90
  have hx229 : Bounds (626914135097 / 500000000000) (1004385861 / 800000000) x229 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x230 : ℝ := x198*(1 / 1)
  have hx230 : Bounds (9302142111 / 10000000000) (582110599 / 625000000) x230 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x231 : ℝ := x198*x230
  have hx231 : Bounds (216324619633 / 250000000000) (867463038639 / 1000000000000) x231 := by
    apply bounds_mul hx198 hx230 <;> norm_num
  let x232 : ℝ := x198^2
  have hx232 : Bounds (216324619633 / 250000000000) (867463038639 / 1000000000000) x232 := by
    (convert hx231 using 1; ring)
  let x233 : ℝ := x229*x232
  have hx233 : Bounds (1084935694539 / 1000000000000) (1089084513687 / 1000000000000) x233 := by
    apply bounds_mul hx229 hx232 <;> norm_num
  let x234 : ℝ := x192*(1 / 1)
  have hx234 : Bounds (1457385547 / 2000000000) (1458634747 / 2000000000) x234 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x235 : ℝ := x192*x234
  have hx235 : Bounds (530993158151 / 1000000000000) (531903831289 / 1000000000000) x235 := by
    apply bounds_mul hx192 hx234 <;> norm_num
  let x236 : ℝ := x192*x235
  have hx236 : Bounds (193465438561 / 500000000000) (387926705191 / 1000000000000) x236 := by
    apply bounds_mul hx192 hx235 <;> norm_num
  let x237 : ℝ := x192^3
  have hx237 : Bounds (193465438561 / 500000000000) (387926705191 / 1000000000000) x237 := by
    (convert hx236 using 1; ring)
  let x238 : ℝ := x233*x237
  have hx238 : Bounds (104948779977 / 250000000000) (42248496707 / 100000000000) x238 := by
    apply bounds_mul hx233 hx237 <;> norm_num
  let x239 : ℝ := x238⁻¹
  have hx239 : Bounds (591737030867 / 250000000000) (1191057199783 / 500000000000) x239 := by
    apply bounds_inv hx238 <;> norm_num
  let x240 : ℝ := x228*x239
  have hx240 : Bounds (1080291706163 / 500000000000) (436035680949 / 200000000000) x240 := by
    apply bounds_mul hx228 hx239 <;> norm_num
  let x241 : ℝ := x228/x238
  have hx241 : Bounds (1080291706163 / 500000000000) (436035680949 / 200000000000) x241 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx240
  let x242 : ℝ := -x209
  have hx242 : Bounds (-270585973 / 1000000000) (-536423323 / 2000000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x243 : ℝ := (2 / 1)*x192
  have hx243 : Bounds (1457385547 / 1000000000) (1458634747 / 1000000000) x243 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x244 : ℝ := c*(1 / 1)
  have hx244 : Bounds (6549 / 25000) (26417 / 100000) x244 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x245 : ℝ := c*x244
  have hx245 : Bounds (42889401 / 625000000) (697857889 / 10000000000) x245 := by
    apply bounds_mul hc hx244 <;> norm_num
  let x246 : ℝ := c^2
  have hx246 : Bounds (42889401 / 625000000) (697857889 / 10000000000) x246 := by
    (convert hx245 using 1; ring)
  let x247 : ℝ := -x246
  have hx247 : Bounds (-697857889 / 10000000000) (-42889401 / 625000000) x247 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx246
  let x248 : ℝ := x243+x247
  have hx248 : Bounds (13875997581 / 10000000000) (6950058527 / 5000000000) x248 := by
    apply bounds_add hx243 hx247 <;> norm_num
  let x249 : ℝ := x243-x246
  have hx249 : Bounds (13875997581 / 10000000000) (6950058527 / 5000000000) x249 := by
    exact hx248
  let x250 : ℝ := x242*x249
  have hx250 : Bounds (-94029417447 / 250000000000) (-46521304577 / 125000000000) x250 := by
    apply bounds_mul hx242 hx249 <;> norm_num
  let x251 : ℝ := x198⁻¹
  have hx251 : Bounds (536839563713 / 500000000000) (268755300679 / 250000000000) x251 := by
    apply bounds_inv hx198 <;> norm_num
  let x252 : ℝ := c*x251
  have hx252 : Bounds (14063049211 / 50000000000) (141994175561 / 500000000000) x252 := by
    apply bounds_mul hc hx251 <;> norm_num
  let x253 : ℝ := c/x198
  have hx253 : Bounds (14063049211 / 50000000000) (141994175561 / 500000000000) x253 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx252
  let x254 : ℝ := (2 / 1)*x253
  have hx254 : Bounds (14063049211 / 25000000000) (141994175561 / 250000000000) x254 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx253 <;> norm_num
  let x255 : ℝ := (2 / 1)*c
  have hx255 : Bounds (6549 / 12500) (26417 / 50000) x255 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hc <;> norm_num
  let x256 : ℝ := -x255
  have hx256 : Bounds (-26417 / 50000) (-6549 / 12500) x256 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx255
  let x257 : ℝ := x254+x256
  have hx257 : Bounds (854549211 / 25000000000) (11014175561 / 250000000000) x257 := by
    apply bounds_add hx254 hx256 <;> norm_num
  let x258 : ℝ := x254-x255
  have hx258 : Bounds (854549211 / 25000000000) (11014175561 / 250000000000) x258 := by
    exact hx257
  let x259 : ℝ := x180*x258
  have hx259 : Bounds (22486152481 / 1000000000000) (7252086179 / 250000000000) x259 := by
    apply bounds_mul hx180 hx258 <;> norm_num
  let x260 : ℝ := x250+x259
  have hx260 : Bounds (-353631517307 / 1000000000000) (-3431620919 / 10000000000) x260 := by
    apply bounds_add hx250 hx259 <;> norm_num
  let x261 : ℝ := (2 / 1)*x90
  have hx261 : Bounds (626914135097 / 500000000000) (1004385861 / 800000000) x261 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx90 <;> norm_num
  let x262 : ℝ := x198*(1 / 1)
  have hx262 : Bounds (9302142111 / 10000000000) (582110599 / 625000000) x262 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x263 : ℝ := x198*x262
  have hx263 : Bounds (216324619633 / 250000000000) (867463038639 / 1000000000000) x263 := by
    apply bounds_mul hx198 hx262 <;> norm_num
  let x264 : ℝ := x198^2
  have hx264 : Bounds (216324619633 / 250000000000) (867463038639 / 1000000000000) x264 := by
    (convert hx263 using 1; ring)
  let x265 : ℝ := x261*x264
  have hx265 : Bounds (1084935694539 / 1000000000000) (1089084513687 / 1000000000000) x265 := by
    apply bounds_mul hx261 hx264 <;> norm_num
  let x266 : ℝ := x192*(1 / 1)
  have hx266 : Bounds (1457385547 / 2000000000) (1458634747 / 2000000000) x266 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x267 : ℝ := x192*x266
  have hx267 : Bounds (530993158151 / 1000000000000) (531903831289 / 1000000000000) x267 := by
    apply bounds_mul hx192 hx266 <;> norm_num
  let x268 : ℝ := x192*x267
  have hx268 : Bounds (193465438561 / 500000000000) (387926705191 / 1000000000000) x268 := by
    apply bounds_mul hx192 hx267 <;> norm_num
  let x269 : ℝ := x192^3
  have hx269 : Bounds (193465438561 / 500000000000) (387926705191 / 1000000000000) x269 := by
    (convert hx268 using 1; ring)
  let x270 : ℝ := x265*x269
  have hx270 : Bounds (104948779977 / 250000000000) (42248496707 / 100000000000) x270 := by
    apply bounds_mul hx265 hx269 <;> norm_num
  let x271 : ℝ := x270⁻¹
  have hx271 : Bounds (591737030867 / 250000000000) (1191057199783 / 500000000000) x271 := by
    apply bounds_inv hx270 <;> norm_num
  let x272 : ℝ := x260*x271
  have hx272 : Bounds (-421195364759 / 500000000000) (-203061717367 / 250000000000) x272 := by
    apply bounds_mul hx260 hx271 <;> norm_num
  let x273 : ℝ := x260/x270
  have hx273 : Bounds (-421195364759 / 500000000000) (-203061717367 / 250000000000) x273 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx272
  let x274 : ℝ := (4 / 1)*c
  have hx274 : Bounds (6549 / 6250) (26417 / 25000) x274 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hc <;> norm_num
  let x275 : ℝ := x198⁻¹
  have hx275 : Bounds (536839563713 / 500000000000) (268755300679 / 250000000000) x275 := by
    apply bounds_inv hx198 <;> norm_num
  let x276 : ℝ := x274*x275
  have hx276 : Bounds (562521968441 / 500000000000) (567976702243 / 500000000000) x276 := by
    apply bounds_mul hx274 hx275 <;> norm_num
  let x277 : ℝ := x274/x198
  have hx277 : Bounds (562521968441 / 500000000000) (567976702243 / 500000000000) x277 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx276
  let x278 : ℝ := (3 / 1)*c
  have hx278 : Bounds (19647 / 25000) (79251 / 100000) x278 := by
    apply bounds_mul (bounds_const ((3 / 1) : ℝ)) hc <;> norm_num
  let x279 : ℝ := x198*x192
  have hx279 : Bounds (135568074687 / 200000000000) (679269397039 / 1000000000000) x279 := by
    apply bounds_mul hx198 hx192 <;> norm_num
  let x280 : ℝ := x279⁻¹
  have hx280 : Bounds (1472169958427 / 1000000000000) (1475273588283 / 1000000000000) x280 := by
    apply bounds_inv hx279 <;> norm_num
  let x281 : ℝ := x278*x280
  have hx281 : Bounds (72309307933 / 62500000000) (1169169071451 / 1000000000000) x281 := by
    apply bounds_mul hx278 hx280 <;> norm_num
  let x282 : ℝ := x278/x279
  have hx282 : Bounds (72309307933 / 62500000000) (1169169071451 / 1000000000000) x282 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx281
  let x283 : ℝ := -x282
  have hx283 : Bounds (-1169169071451 / 1000000000000) (-72309307933 / 62500000000) x283 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx282
  let x284 : ℝ := x277+x283
  have hx284 : Bounds (-44125134569 / 1000000000000) (-10497761221 / 500000000000) x284 := by
    apply bounds_add hx277 hx283 <;> norm_num
  let x285 : ℝ := x277-x282
  have hx285 : Bounds (-44125134569 / 1000000000000) (-10497761221 / 500000000000) x285 := by
    exact hx284
  let x286 : ℝ := x241*x285
  have hx286 : Bounds (-48100332747 / 500000000000) (-45362577521 / 1000000000000) x286 := by
    apply bounds_mul hx241 hx285 <;> norm_num
  let x287 : ℝ := x273+x286
  have hx287 : Bounds (-234647848753 / 250000000000) (-857609446989 / 1000000000000) x287 := by
    apply bounds_add hx273 hx286 <;> norm_num
  let x288 : ℝ := (2 / 1)*x192
  have hx288 : Bounds (1457385547 / 1000000000) (1458634747 / 1000000000) x288 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx192 <;> norm_num
  let x289 : ℝ := c*(1 / 1)
  have hx289 : Bounds (6549 / 25000) (26417 / 100000) x289 := by
    apply bounds_mul hc (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x290 : ℝ := c*x289
  have hx290 : Bounds (42889401 / 625000000) (697857889 / 10000000000) x290 := by
    apply bounds_mul hc hx289 <;> norm_num
  let x291 : ℝ := c^2
  have hx291 : Bounds (42889401 / 625000000) (697857889 / 10000000000) x291 := by
    (convert hx290 using 1; ring)
  let x292 : ℝ := -x291
  have hx292 : Bounds (-697857889 / 10000000000) (-42889401 / 625000000) x292 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx291
  let x293 : ℝ := x288+x292
  have hx293 : Bounds (13875997581 / 10000000000) (6950058527 / 5000000000) x293 := by
    apply bounds_add hx288 hx292 <;> norm_num
  let x294 : ℝ := x288-x291
  have hx294 : Bounds (13875997581 / 10000000000) (6950058527 / 5000000000) x294 := by
    exact hx293
  let x295 : ℝ := c*x294
  have hx295 : Bounds (363495632631 / 1000000000000) (45899924027 / 125000000000) x295 := by
    apply bounds_mul hc hx294 <;> norm_num
  let x296 : ℝ := x198*(1 / 1)
  have hx296 : Bounds (9302142111 / 10000000000) (582110599 / 625000000) x296 := by
    apply bounds_mul hx198 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x297 : ℝ := x198*x296
  have hx297 : Bounds (216324619633 / 250000000000) (867463038639 / 1000000000000) x297 := by
    apply bounds_mul hx198 hx296 <;> norm_num
  let x298 : ℝ := x198^2
  have hx298 : Bounds (216324619633 / 250000000000) (867463038639 / 1000000000000) x298 := by
    (convert hx297 using 1; ring)
  let x299 : ℝ := x192*(1 / 1)
  have hx299 : Bounds (1457385547 / 2000000000) (1458634747 / 2000000000) x299 := by
    apply bounds_mul hx192 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x300 : ℝ := x192*x299
  have hx300 : Bounds (530993158151 / 1000000000000) (531903831289 / 1000000000000) x300 := by
    apply bounds_mul hx192 hx299 <;> norm_num
  let x301 : ℝ := x192^2
  have hx301 : Bounds (530993158151 / 1000000000000) (531903831289 / 1000000000000) x301 := by
    (convert hx300 using 1; ring)
  let x302 : ℝ := x298*x301
  have hx302 : Bounds (229733785929 / 500000000000) (230703456877 / 500000000000) x302 := by
    apply bounds_mul hx298 hx301 <;> norm_num
  let x303 : ℝ := x302⁻¹
  have hx303 : Bounds (433456877299 / 200000000000) (1088216080143 / 500000000000) x303 := by
    apply bounds_inv hx302 <;> norm_num
  let x304 : ℝ := x295*x303
  have hx304 : Bounds (19694960229 / 25000000000) (799184566457 / 1000000000000) x304 := by
    apply bounds_mul hx295 hx303 <;> norm_num
  let x305 : ℝ := x295/x302
  have hx305 : Bounds (19694960229 / 25000000000) (799184566457 / 1000000000000) x305 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx304
  let x306 : ℝ := c*x220
  have hx306 : Bounds (71948118741 / 500000000000) (18271125949 / 125000000000) x306 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x307 : ℝ := x180+x306
  have hx307 : Bounds (400866456497 / 500000000000) (402300528123 / 500000000000) x307 := by
    apply bounds_add hx180 hx306 <;> norm_num
  let x308 : ℝ := x307*(1 / 1)
  have hx308 : Bounds (400866456497 / 500000000000) (402300528123 / 500000000000) x308 := by
    apply bounds_mul hx307 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x309 : ℝ := x307*x308
  have hx309 : Bounds (642775663777 / 1000000000000) (647382859713 / 1000000000000) x309 := by
    apply bounds_mul hx307 hx308 <;> norm_num
  let x310 : ℝ := x307^2
  have hx310 : Bounds (642775663777 / 1000000000000) (647382859713 / 1000000000000) x310 := by
    (convert hx309 using 1; ring)
  let x311 : ℝ := x287*x310
  have hx311 : Bounds (-121525596281 / 200000000000) (-551250481549 / 1000000000000) x311 := by
    apply bounds_mul hx287 hx310 <;> norm_num
  let x312 : ℝ := (2 / 1)*x241
  have hx312 : Bounds (1080291706163 / 250000000000) (436035680949 / 100000000000) x312 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx241 <;> norm_num
  let x313 : ℝ := c*x220
  have hx313 : Bounds (71948118741 / 500000000000) (18271125949 / 125000000000) x313 := by
    apply bounds_mul hc hx220 <;> norm_num
  let x314 : ℝ := x180+x313
  have hx314 : Bounds (400866456497 / 500000000000) (402300528123 / 500000000000) x314 := by
    apply bounds_add hx180 hx313 <;> norm_num
  let x315 : ℝ := x312*x314
  have hx315 : Bounds (3464421665861 / 1000000000000) (1754173847263 / 500000000000) x315 := by
    apply bounds_mul hx312 hx314 <;> norm_num
  let x316 : ℝ := -x209
  have hx316 : Bounds (-270585973 / 1000000000) (-536423323 / 2000000000) x316 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx209
  let x317 : ℝ := x220+x316
  have hx317 : Bounds (278720171 / 1000000000) (285102521 / 1000000000) x317 := by
    apply bounds_add hx220 hx316 <;> norm_num
  let x318 : ℝ := x220-x209
  have hx318 : Bounds (278720171 / 1000000000) (285102521 / 1000000000) x318 := by
    exact hx317
  let x319 : ℝ := x315*x318
  have hx319 : Bounds (241401049781 / 250000000000) (500119386127 / 500000000000) x319 := by
    apply bounds_mul hx315 hx318 <;> norm_num
  let x320 : ℝ := x311+x319
  have hx320 : Bounds (357976217719 / 1000000000000) (89797658141 / 200000000000) x320 := by
    apply bounds_add hx311 hx319 <;> norm_num
  let x321 : ℝ := a*(1 / 1)
  have hx321 : Bounds (1 / 2) (503 / 1000) x321 := by
    apply bounds_mul ha (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x322 : ℝ := a*x321
  have hx322 : Bounds (1 / 4) (253009 / 1000000) x322 := by
    apply bounds_mul ha hx321 <;> norm_num
  let x323 : ℝ := a^2
  have hx323 : Bounds (1 / 4) (253009 / 1000000) x323 := by
    (convert hx322 using 1; ring)
  let x324 : ℝ := -x323
  have hx324 : Bounds (-253009 / 1000000) (-1 / 4) x324 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx323
  let x325 : ℝ := (1 / 1)+x324
  have hx325 : Bounds (746991 / 1000000) (3 / 4) x325 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx324 <;> norm_num
  let x326 : ℝ := (1 / 1)-x323
  have hx326 : Bounds (746991 / 1000000) (3 / 4) x326 := by
    exact hx325
  let x327 : ℝ := x326⁻¹
  have hx327 : Bounds (1333333333333 / 1000000000000) (1338704214643 / 1000000000000) x327 := by
    apply bounds_inv hx326 <;> norm_num
  let x328 : ℝ := (1 / 1)*x327
  have hx328 : Bounds (1333333333333 / 1000000000000) (1338704214643 / 1000000000000) x328 := by
    apply bounds_mul (bounds_const ((1 / 1) : ℝ)) hx327 <;> norm_num
  let x329 : ℝ := (1 / 1)/x326
  have hx329 : Bounds (1333333333333 / 1000000000000) (1338704214643 / 1000000000000) x329 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx328
  let x330 : ℝ := x329*x305
  have hx330 : Bounds (1050397878879 / 1000000000000) (534935873697 / 500000000000) x330 := by
    apply bounds_mul hx329 hx305 <;> norm_num
  let x331 : ℝ := x320+x330
  have hx331 : Bounds (704187048299 / 500000000000) (1518860038099 / 1000000000000) x331 := by
    apply bounds_add hx320 hx330 <;> norm_num
  let x332 : ℝ := x180*(1 / 1)
  have hx332 : Bounds (82229584439 / 125000000000) (329216024327 / 500000000000) x332 := by
    apply bounds_mul hx180 (bounds_const ((1 / 1) : ℝ)) <;> norm_num
  let x333 : ℝ := x180*x332
  have hx333 : Bounds (6761704557 / 15625000000) (86706552539 / 200000000000) x333 := by
    apply bounds_mul hx180 hx332 <;> norm_num
  let x334 : ℝ := x180^2
  have hx334 : Bounds (6761704557 / 15625000000) (86706552539 / 200000000000) x334 := by
    (convert hx333 using 1; ring)
  let x335 : ℝ := x331*x334
  have hx335 : Bounds (609472611003 / 1000000000000) (131695117693 / 200000000000) x335 := by
    apply bounds_mul hx331 hx334 <;> norm_num
  let x336 : ℝ := x90*x192
  have hx336 : Bounds (9136555997 / 20000000000) (457822536329 / 1000000000000) x336 := by
    apply bounds_mul hx90 hx192 <;> norm_num
  let x337 : ℝ := x336⁻¹
  have hx337 : Bounds (436850491467 / 200000000000) (218900863811 / 100000000000) x337 := by
    apply bounds_inv hx336 <;> norm_num
  let x338 : ℝ := x335*x337
  have hx338 : Bounds (1331242048261 / 1000000000000) (288281750227 / 200000000000) x338 := by
    apply bounds_mul hx335 hx337 <;> norm_num
  let x339 : ℝ := x335/x336
  have hx339 : Bounds (1331242048261 / 1000000000000) (288281750227 / 200000000000) x339 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx338
  have hu : x339 < (5794535752043 / 3600000000000) := lt_of_le_of_lt hx339.2 (by norm_num)
  simpa +zetaDelta only [ScFormula,Kprime,K,Mprime,SmallMean.A,biasB,div_one,pow_two] using hu

open GeneralCK.Reflection
/-- Uniform derivative enclosure including input boxes with z=0. -/
theorem derivative_bound_900 {a z s : ℝ}
    (ha : a ∈ Set.Icc ((1 / 2):ℝ) ((503 / 1000)))
    (hz : z ∈ Set.Icc (0:ℝ) (1/1000))
    (hs : s ∈ Set.Ioo (a*(1-z)/2) (a*(1+z)/2)) :
    P a ((biasE a+biasE (a*z))/2) s ≤ (5794535752043 / 3600000000000) := by
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
  have hsl : (999 / 4000) ≤ s := by
    have h := mul_le_mul ha.1 (show (999/1000:ℝ) ≤ 1-z by linarith [hz.2])
      (by norm_num : (0:ℝ) ≤ 999/1000) ha0.le
    nlinarith [hs.1]
  have hsu : s ≤ (503503 / 2000000) := by
    have h := mul_le_mul ha.2 (show 1+z ≤ (1001/1000:ℝ) by linarith [hz.2])
      (by linarith [hz.1] : 0 ≤ 1+z) (by norm_num : (0:ℝ) ≤ (503 / 1000))
    nlinarith [hs.2]
  have hy := div_pos he hs0
  have hc := biasContact_mem hy
  have heq : biasE (biasContact (((biasE a+biasE (a*z))/2)/s)) =
      (((biasE a+biasE (a*z))/2)/s)*biasContact (((biasE a+biasE (a*z))/2)/s) := by
    exact (div_eq_iff hc.1.ne').mp (biasR_biasContact hy)
  have hb := derivative_leaf_900 a z s _ ha hz ⟨hsl,hsu⟩ hc.1.le hc.2.le heq
  rw [P_eq_formula ha0 ha1 he hs0]
  exact hb.le

/-- Checked low-ratio strip: includes arbitrarily small positive z. -/
theorem curvature_leaf_900 {a z : ℝ}
    (ha : a ∈ Set.Icc ((1 / 2):ℝ) ((503 / 1000)))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < curvature a (a*z) := by
  have ha0 : 0 < a := by linarith [ha.1]
  have ha1 : a < 1 := by linarith [ha.2]
  apply curvature_pos_of_derivative_bound ha0 ha1 hz.1 (by linarith [hz.2])
    (fun s hs => derivative_bound_900 ha ⟨hz.1.le,hz.2⟩ hs) (M := (5794535752043 / 3600000000000))
  exact lt_of_lt_of_le (by norm_num : (5794535752043 / 3600000000000) < 2*((1 / 2):ℝ)/(1-((1 / 2):ℝ)^2)^2)
    (base_mono (by norm_num) ha.1 ha1)

end GeneralCK.Certificates.LowRatioFamily

end


