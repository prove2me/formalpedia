-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell213__4
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell213__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T14:42:06.151493+00:00
-- url     : https://prove2.me/theorems/1a1be4fa-7a3c-42f5-8739-e7321c7dc854
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell213 (+3 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell214, Ge…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell213 (+3 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell214, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell215, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell216)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell213 (+3 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell214, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell215, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell216)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell213 (+3 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell214, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell215, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell216) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell213 (+3 modules: GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell214, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell215, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell216).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapHighMiddleDerivativeTraceForm
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell209Logs__6
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell215Logs__4

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell213 =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell213
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_derivative_pos (x : ℝ)
    (hx : Bounds (1919 / 10240) (961 / 5120) x) :
    0 < doubleCapBridgeDerivativeExpression x := by
  have hxPos0 : 0 < x := by linarith [hx.1]
  have hxHalf : x < 1 / 2 := by linarith [hx.2]
  have hh0 : 0 < doubleCapHighTailFloor x :=
    doubleCapHighTailFloor_pos hxPos0 hxHalf
  have hh1 : doubleCapHighTailFloor x < 1 := by
    have hfloor := doubleCapHighFloor_lt_entropyCap
      (m := (1 - x) / 2) (by linarith) (by linarith)
    have hH1 := H_le_one ((1 - x) / 2)
    unfold doubleCapHighTailFloor
    have heq : 2 * ((1 - x) / 2) - 1 / 2 =
        (1 - 2 * x) / 2 := by ring
    rw [heq] at hfloor
    linarith
  have hEq : biasE (2 * x) = Real.log 2 * H ((1 - 2 * x) / 2) := by
    rw [show 2 * x = 1 - 2 * ((1 - 2 * x) / 2) by ring,
      GeneralCK.Correction.Natural.biasE_probability (by linarith)
        (by linarith), GeneralCK.Certificates.Mixed.hn_eq_H_mul_log]
    ring
  have hEll : Real.log 2 * doubleCapHighTailFloor x =
      (Real.log 2 + biasE (2 * x)) / 2 := by
    dsimp [doubleCapHighTailFloor]
    rw [hEq]
    ring
  let x0 : ℝ := (2 / 1)*x
  have hx0 : Bounds (1919 / 5120) (961 / 2560) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx <;> norm_num
  let x1 : ℝ := Real.log (2 / 1)
  have hx1 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x1 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x2 : ℝ := Real.log (2 / 1)
  have hx2 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x2 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x3 : ℝ := (1 / 1)+(961 / 2560)
  have hx3 : Bounds (3521 / 2560) (3521 / 2560) x3 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((961 / 2560) : ℝ)) <;> norm_num
  let x4 : ℝ := (1 / 1)+(961 / 2560)
  have hx4 : Bounds (3521 / 2560) (3521 / 2560) x4 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((961 / 2560) : ℝ)) <;> norm_num
  let x5 : ℝ := Real.log x4
  have hx5 : Bounds (318737781 / 1000000000) (159368891 / 500000000) x5 := by
    exact bounds_log hx4 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x6 : ℝ := x3*x5
  have hx6 : Bounds (21919447791 / 50000000000) (438388957197 / 1000000000000) x6 := by
    apply bounds_mul hx3 hx5 <;> norm_num
  let x7 : ℝ := -(961 / 2560)
  have hx7 : Bounds (-961 / 2560) (-961 / 2560) x7 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((961 / 2560) : ℝ))
  let x8 : ℝ := (1 / 1)+x7
  have hx8 : Bounds (1599 / 2560) (1599 / 2560) x8 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx7 <;> norm_num
  let x9 : ℝ := (1 / 1)-(961 / 2560)
  have hx9 : Bounds (1599 / 2560) (1599 / 2560) x9 := by
    exact hx8
  let x10 : ℝ := -(961 / 2560)
  have hx10 : Bounds (-961 / 2560) (-961 / 2560) x10 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((961 / 2560) : ℝ))
  let x11 : ℝ := (1 / 1)+x10
  have hx11 : Bounds (1599 / 2560) (1599 / 2560) x11 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx10 <;> norm_num
  let x12 : ℝ := (1 / 1)-(961 / 2560)
  have hx12 : Bounds (1599 / 2560) (1599 / 2560) x12 := by
    exact hx11
  let x13 : ℝ := Real.log x12
  have hx13 : Bounds (-18825153 / 40000000) (-58828603 / 125000000) x13 := by
    exact bounds_log hx12 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x14 : ℝ := x9*x13
  have hx14 : Bounds (-293959176241 / 1000000000000) (-58791835123 / 200000000000) x14 := by
    apply bounds_mul hx9 hx13 <;> norm_num
  let x15 : ℝ := x6+x14
  have hx15 : Bounds (144429779579 / 1000000000000) (72214890791 / 500000000000) x15 := by
    apply bounds_add hx6 hx14 <;> norm_num
  let x16 : ℝ := (2 / 1)⁻¹
  have hx16 : Bounds (1 / 2) (1 / 2) x16 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x17 : ℝ := x15*x16
  have hx17 : Bounds (72214889789 / 1000000000000) (72214890791 / 1000000000000) x17 := by
    apply bounds_mul hx15 hx16 <;> norm_num
  let x18 : ℝ := x15/(2 / 1)
  have hx18 : Bounds (72214889789 / 1000000000000) (72214890791 / 1000000000000) x18 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx17
  let x19 : ℝ := -x18
  have hx19 : Bounds (-72214890791 / 1000000000000) (-72214889789 / 1000000000000) x19 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx18
  let x20 : ℝ := x2+x19
  have hx20 : Bounds (620932289209 / 1000000000000) (620932291211 / 1000000000000) x20 := by
    apply bounds_add hx2 hx19 <;> norm_num
  let x21 : ℝ := x2-x18
  have hx21 : Bounds (620932289209 / 1000000000000) (620932291211 / 1000000000000) x21 := by
    exact hx20
  let x22 : ℝ := biasE (961 / 2560)
  have hx22 : Bounds (620932289209 / 1000000000000) (620932291211 / 1000000000000) x22 := by
    simpa +zetaDelta only [biasE, div_one] using hx21
  let x23 : ℝ := Real.log (2 / 1)
  have hx23 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x23 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x24 : ℝ := (1 / 1)+(1919 / 5120)
  have hx24 : Bounds (7039 / 5120) (7039 / 5120) x24 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1919 / 5120) : ℝ)) <;> norm_num
  let x25 : ℝ := (1 / 1)+(1919 / 5120)
  have hx25 : Bounds (7039 / 5120) (7039 / 5120) x25 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1919 / 5120) : ℝ)) <;> norm_num
  let x26 : ℝ := Real.log x25
  have hx26 : Bounds (12732467 / 40000000) (79577919 / 250000000) x26 := by
    exact bounds_log hx25 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x27 : ℝ := x24*x26
  have hx27 : Bounds (3500931063 / 8000000000) (437616384251 / 1000000000000) x27 := by
    apply bounds_mul hx24 hx26 <;> norm_num
  let x28 : ℝ := -(1919 / 5120)
  have hx28 : Bounds (-1919 / 5120) (-1919 / 5120) x28 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1919 / 5120) : ℝ))
  let x29 : ℝ := (1 / 1)+x28
  have hx29 : Bounds (3201 / 5120) (3201 / 5120) x29 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx28 <;> norm_num
  let x30 : ℝ := (1 / 1)-(1919 / 5120)
  have hx30 : Bounds (3201 / 5120) (3201 / 5120) x30 := by
    exact hx29
  let x31 : ℝ := -(1919 / 5120)
  have hx31 : Bounds (-1919 / 5120) (-1919 / 5120) x31 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1919 / 5120) : ℝ))
  let x32 : ℝ := (1 / 1)+x31
  have hx32 : Bounds (3201 / 5120) (3201 / 5120) x32 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx31 <;> norm_num
  let x33 : ℝ := (1 / 1)-(1919 / 5120)
  have hx33 : Bounds (3201 / 5120) (3201 / 5120) x33 := by
    exact hx32
  let x34 : ℝ := Real.log x33
  have hx34 : Bounds (-469691179 / 1000000000) (-234845589 / 500000000) x34 := by
    exact bounds_log hx33 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x35 : ℝ := x30*x34
  have hx35 : Bounds (-146824361717 / 500000000000) (-36706090351 / 125000000000) x35 := by
    apply bounds_mul hx30 hx34 <;> norm_num
  let x36 : ℝ := x27+x35
  have hx36 : Bounds (143967659441 / 1000000000000) (143967661443 / 1000000000000) x36 := by
    apply bounds_add hx27 hx35 <;> norm_num
  let x37 : ℝ := (2 / 1)⁻¹
  have hx37 : Bounds (1 / 2) (1 / 2) x37 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x38 : ℝ := x36*x37
  have hx38 : Bounds (1799595743 / 25000000000) (35991915361 / 500000000000) x38 := by
    apply bounds_mul hx36 hx37 <;> norm_num
  let x39 : ℝ := x36/(2 / 1)
  have hx39 : Bounds (1799595743 / 25000000000) (35991915361 / 500000000000) x39 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx38
  let x40 : ℝ := -x39
  have hx40 : Bounds (-35991915361 / 500000000000) (-1799595743 / 25000000000) x40 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx39
  let x41 : ℝ := x23+x40
  have hx41 : Bounds (310581674639 / 500000000000) (7764541891 / 12500000000) x41 := by
    apply bounds_add hx23 hx40 <;> norm_num
  let x42 : ℝ := x23-x39
  have hx42 : Bounds (310581674639 / 500000000000) (7764541891 / 12500000000) x42 := by
    exact hx41
  let x43 : ℝ := biasE (1919 / 5120)
  have hx43 : Bounds (310581674639 / 500000000000) (7764541891 / 12500000000) x43 := by
    simpa +zetaDelta only [biasE, div_one] using hx42
  let x44 : ℝ := biasE x0
  have hx44 : Bounds (620932289209 / 1000000000000) (7764541891 / 12500000000) x44 := by
    exact bounds_biasE hx0 (by norm_num) (by norm_num) hx22.1 hx43.2
  let x45 : ℝ := x1+x44
  have hx45 : Bounds (1314079469209 / 1000000000000) (32857763307 / 25000000000) x45 := by
    apply bounds_add hx1 hx44 <;> norm_num
  let x46 : ℝ := (2 / 1)⁻¹
  have hx46 : Bounds (1 / 2) (1 / 2) x46 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x47 : ℝ := x45*x46
  have hx47 : Bounds (164259933651 / 250000000000) (32857763307 / 50000000000) x47 := by
    apply bounds_mul hx45 hx46 <;> norm_num
  let x48 : ℝ := x45/(2 / 1)
  have hx48 : Bounds (164259933651 / 250000000000) (32857763307 / 50000000000) x48 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx47
  let x49 : ℝ := Real.log (2 / 1)
  have hx49 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x49 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x50 : ℝ := (1 / 1)+(10667 / 40000)
  have hx50 : Bounds (50667 / 40000) (50667 / 40000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((10667 / 40000) : ℝ)) <;> norm_num
  let x51 : ℝ := (1 / 1)+(10667 / 40000)
  have hx51 : Bounds (50667 / 40000) (50667 / 40000) x51 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((10667 / 40000) : ℝ)) <;> norm_num
  let x52 : ℝ := Real.log x51
  have hx52 : Bounds (59098839 / 250000000) (236395357 / 1000000000) x52 := by
    exact bounds_log hx51 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x53 : ℝ := x50*x52
  have hx53 : Bounds (299436087561 / 1000000000000) (74859022207 / 250000000000) x53 := by
    apply bounds_mul hx50 hx52 <;> norm_num
  let x54 : ℝ := -(10667 / 40000)
  have hx54 : Bounds (-10667 / 40000) (-10667 / 40000) x54 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((10667 / 40000) : ℝ))
  let x55 : ℝ := (1 / 1)+x54
  have hx55 : Bounds (29333 / 40000) (29333 / 40000) x55 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx54 <;> norm_num
  let x56 : ℝ := (1 / 1)-(10667 / 40000)
  have hx56 : Bounds (29333 / 40000) (29333 / 40000) x56 := by
    exact hx55
  let x57 : ℝ := -(10667 / 40000)
  have hx57 : Bounds (-10667 / 40000) (-10667 / 40000) x57 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((10667 / 40000) : ℝ))
  let x58 : ℝ := (1 / 1)+x57
  have hx58 : Bounds (29333 / 40000) (29333 / 40000) x58 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx57 <;> norm_num
  let x59 : ℝ := (1 / 1)-(10667 / 40000)
  have hx59 : Bounds (29333 / 40000) (29333 / 40000) x59 := by
    exact hx58
  let x60 : ℝ := Real.log x59
  have hx60 : Bounds (-310166293 / 1000000000) (-77541573 / 250000000) x60 := by
    exact bounds_log hx59 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x61 : ℝ := x56*x60
  have hx61 : Bounds (-45490539363 / 200000000000) (-2843158701 / 12500000000) x61 := by
    apply bounds_mul hx56 hx60 <;> norm_num
  let x62 : ℝ := x53+x61
  have hx62 : Bounds (35991695373 / 500000000000) (17995848187 / 250000000000) x62 := by
    apply bounds_add hx53 hx61 <;> norm_num
  let x63 : ℝ := (2 / 1)⁻¹
  have hx63 : Bounds (1 / 2) (1 / 2) x63 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x64 : ℝ := x62*x63
  have hx64 : Bounds (35991695373 / 1000000000000) (17995848187 / 500000000000) x64 := by
    apply bounds_mul hx62 hx63 <;> norm_num
  let x65 : ℝ := x62/(2 / 1)
  have hx65 : Bounds (35991695373 / 1000000000000) (17995848187 / 500000000000) x65 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx64
  let x66 : ℝ := -x65
  have hx66 : Bounds (-17995848187 / 500000000000) (-35991695373 / 1000000000000) x66 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx65
  let x67 : ℝ := x49+x66
  have hx67 : Bounds (328577741813 / 500000000000) (657155485627 / 1000000000000) x67 := by
    apply bounds_add hx49 hx66 <;> norm_num
  let x68 : ℝ := x49-x65
  have hx68 : Bounds (328577741813 / 500000000000) (657155485627 / 1000000000000) x68 := by
    exact hx67
  let x69 : ℝ := biasE (10667 / 40000)
  have hx69 : Bounds (328577741813 / 500000000000) (657155485627 / 1000000000000) x69 := by
    simpa +zetaDelta only [biasE, div_one] using hx68
  let x70 : ℝ := Real.log (2 / 1)
  have hx70 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x70 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x71 : ℝ := (1 / 1)+(267099 / 1000000)
  have hx71 : Bounds (1267099 / 1000000) (1267099 / 1000000) x71 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((267099 / 1000000) : ℝ)) <;> norm_num
  let x72 : ℝ := (1 / 1)+(267099 / 1000000)
  have hx72 : Bounds (1267099 / 1000000) (1267099 / 1000000) x72 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((267099 / 1000000) : ℝ)) <;> norm_num
  let x73 : ℝ := Real.log x72
  have hx73 : Bounds (47346007 / 200000000) (59182509 / 250000000) x73 := by
    exact bounds_log hx72 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x74 : ℝ := x71*x73
  have hx74 : Bounds (149980195309 / 500000000000) (149980195943 / 500000000000) x74 := by
    apply bounds_mul hx71 hx73 <;> norm_num
  let x75 : ℝ := -(267099 / 1000000)
  have hx75 : Bounds (-267099 / 1000000) (-267099 / 1000000) x75 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((267099 / 1000000) : ℝ))
  let x76 : ℝ := (1 / 1)+x75
  have hx76 : Bounds (732901 / 1000000) (732901 / 1000000) x76 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx75 <;> norm_num
  let x77 : ℝ := (1 / 1)-(267099 / 1000000)
  have hx77 : Bounds (732901 / 1000000) (732901 / 1000000) x77 := by
    exact hx76
  let x78 : ℝ := -(267099 / 1000000)
  have hx78 : Bounds (-267099 / 1000000) (-267099 / 1000000) x78 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((267099 / 1000000) : ℝ))
  let x79 : ℝ := (1 / 1)+x78
  have hx79 : Bounds (732901 / 1000000) (732901 / 1000000) x79 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx78 <;> norm_num
  let x80 : ℝ := (1 / 1)-(267099 / 1000000)
  have hx80 : Bounds (732901 / 1000000) (732901 / 1000000) x80 := by
    exact hx79
  let x81 : ℝ := Real.log x80
  have hx81 : Bounds (-38843081 / 125000000) (-310744647 / 1000000000) x81 := by
    exact bounds_log hx80 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x82 : ℝ := x77*x81
  have hx82 : Bounds (-7117033227 / 31250000000) (-22774506253 / 100000000000) x82 := by
    apply bounds_mul hx77 hx81 <;> norm_num
  let x83 : ℝ := x74+x82
  have hx83 : Bounds (36107663677 / 500000000000) (18053832339 / 250000000000) x83 := by
    apply bounds_add hx74 hx82 <;> norm_num
  let x84 : ℝ := (2 / 1)⁻¹
  have hx84 : Bounds (1 / 2) (1 / 2) x84 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x85 : ℝ := x83*x84
  have hx85 : Bounds (36107663677 / 1000000000000) (18053832339 / 500000000000) x85 := by
    apply bounds_mul hx83 hx84 <;> norm_num
  let x86 : ℝ := x83/(2 / 1)
  have hx86 : Bounds (36107663677 / 1000000000000) (18053832339 / 500000000000) x86 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx85
  let x87 : ℝ := -x86
  have hx87 : Bounds (-18053832339 / 500000000000) (-36107663677 / 1000000000000) x87 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx86
  let x88 : ℝ := x70+x87
  have hx88 : Bounds (328519757661 / 500000000000) (657039517323 / 1000000000000) x88 := by
    apply bounds_add hx70 hx87 <;> norm_num
  let x89 : ℝ := x70-x86
  have hx89 : Bounds (328519757661 / 500000000000) (657039517323 / 1000000000000) x89 := by
    exact hx88
  let x90 : ℝ := biasE (267099 / 1000000)
  have hx90 : Bounds (328519757661 / 500000000000) (657039517323 / 1000000000000) x90 := by
    simpa +zetaDelta only [biasE, div_one] using hx89
  let y : ℝ := doubleCapHighTailY x
  have hEll' : Real.log 2 * doubleCapHighTailFloor x = x48 := by
    simpa +zetaDelta only [div_one] using hEll
  have hy : Bounds (10667 / 40000) (267099 / 1000000) y := by
    dsimp only [y, doubleCapHighTailY]
    apply entropyInverseBias_bracket hh0.le hh1.le
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (267099 / 1000000) ≤ (657039517323 / 1000000000000) := hx90.2
      have h2 : (164259933651 / 250000000000) ≤ x48 := hx48.1
      linarith [hEll']
    · have h1 : x48 ≤ (32857763307 / 50000000000) := hx48.2
      have h2 : (328577741813 / 500000000000) ≤ biasE (10667 / 40000) := hx69.1
      linarith [hEll']
  let x91 : ℝ := x⁻¹
  have hx91 : Bounds (665972944849 / 125000000000) (42688900469 / 8000000000) x91 := by
    apply bounds_inv hx <;> norm_num
  let x92 : ℝ := x48*x91
  have hx92 : Bounds (437570686937 / 125000000000) (3506654468617 / 1000000000000) x92 := by
    apply bounds_mul hx48 hx91 <;> norm_num
  let x93 : ℝ := x48/x
  have hx93 : Bounds (437570686937 / 125000000000) (3506654468617 / 1000000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(192357 / 1000000)
  have hx95 : Bounds (1192357 / 1000000) (1192357 / 1000000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((192357 / 1000000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(192357 / 1000000)
  have hx96 : Bounds (1192357 / 1000000) (1192357 / 1000000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((192357 / 1000000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (8796601 / 50000000) (175932021 / 1000000000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (209773775571 / 1000000000000) (52443444191 / 250000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(192357 / 1000000)
  have hx99 : Bounds (-192357 / 1000000) (-192357 / 1000000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((192357 / 1000000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (807643 / 1000000) (807643 / 1000000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(192357 / 1000000)
  have hx101 : Bounds (807643 / 1000000) (807643 / 1000000) x101 := by
    exact hx100
  let x102 : ℝ := -(192357 / 1000000)
  have hx102 : Bounds (-192357 / 1000000) (-192357 / 1000000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((192357 / 1000000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (807643 / 1000000) (807643 / 1000000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(192357 / 1000000)
  have hx104 : Bounds (807643 / 1000000) (807643 / 1000000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-4272703 / 20000000) (-213635149 / 1000000000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-43135233363 / 250000000000) (-172540932643 / 1000000000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (37232842119 / 1000000000000) (37232844121 / 1000000000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (18616421059 / 1000000000000) (18616422061 / 1000000000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (18616421059 / 1000000000000) (18616422061 / 1000000000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-18616422061 / 1000000000000) (-18616421059 / 1000000000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (674530757939 / 1000000000000) (674530759941 / 1000000000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (674530757939 / 1000000000000) (674530759941 / 1000000000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (192357 / 1000000)
  have hx114 : Bounds (674530757939 / 1000000000000) (674530759941 / 1000000000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(7707 / 40000)
  have hx116 : Bounds (47707 / 40000) (47707 / 40000) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((7707 / 40000) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(7707 / 40000)
  have hx117 : Bounds (47707 / 40000) (47707 / 40000) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((7707 / 40000) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (176198683 / 1000000000) (44049671 / 250000000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (210147764247 / 1000000000000) (656711767 / 3125000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(7707 / 40000)
  have hx120 : Bounds (-7707 / 40000) (-7707 / 40000) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((7707 / 40000) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (32293 / 40000) (32293 / 40000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(7707 / 40000)
  have hx122 : Bounds (32293 / 40000) (32293 / 40000) x122 := by
    exact hx121
  let x123 : ℝ := -(7707 / 40000)
  have hx123 : Bounds (-7707 / 40000) (-7707 / 40000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((7707 / 40000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (32293 / 40000) (32293 / 40000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(7707 / 40000)
  have hx125 : Bounds (32293 / 40000) (32293 / 40000) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-107014483 / 500000000) (-42805793 / 200000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-2699858359 / 15625000000) (-21598866771 / 125000000000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (37356829271 / 1000000000000) (4669603909 / 125000000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (3735682927 / 200000000000) (4669603909 / 250000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (3735682927 / 200000000000) (4669603909 / 250000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-4669603909 / 250000000000) (-3735682927 / 200000000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (168617191091 / 250000000000) (134893753273 / 200000000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (168617191091 / 250000000000) (134893753273 / 200000000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (7707 / 40000)
  have hx135 : Bounds (168617191091 / 250000000000) (134893753273 / 200000000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(192357 / 1000000)
  have hx136 : Bounds (673358277017 / 1000000000000) (33726476681 / 50000000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((192357 / 1000000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(7707 / 40000)
  have hx137 : Bounds (168617864211 / 250000000000) (675644649741 / 1000000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((7707 / 40000) : ℝ)) <;> norm_num
  let c : ℝ := doubleCapHighTailC x
  have hcMem := Reflection.regularContact_mem
    (x / (Real.log 2 * doubleCapHighTailFloor x))
  have hc0 : 0 ≤ c := by
    dsimp only [c, doubleCapHighTailC]
    apply GeneralCK.Certificates.RegularContactBounds.regularContact_nonneg
    exact div_nonneg hxPos0.le ((mul_pos log_two_pos hh0).le)
  have hcEq : biasE c = x93 * c := by
    have he := doubleCapHighTailC_equation x
    change c = (x / (Real.log 2 * doubleCapHighTailFloor x)) * biasE c at he
    rw [hEll'] at he
    have hxPos : 0 < x := hxPos0
    have hEllPos : 0 < x48 := by rw [← hEll']; exact mul_pos log_two_pos hh0
    change biasE c = (x48 / x) * c
    field_simp [hxPos.ne', hEllPos.ne'] at he ⊢
    nlinarith
  have hc : Bounds (192357 / 1000000) (7707 / 40000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num)
      (by norm_num) (show 0 < x93 by linarith [hx93.1]) hcEq
    · have h1 : x93 * (192357 / 1000000) ≤ (33726476681 / 50000000000) := hx136.2
      have h2 : (674530757939 / 1000000000000) ≤ biasE (192357 / 1000000) := hx114.1
      linarith
    · have h1 : biasE (7707 / 40000) ≤ (134893753273 / 200000000000) := hx135.2
      have h2 : (168617864211 / 250000000000) ≤ x93 * (7707 / 40000) := hx137.1
      linarith
  let x138 : ℝ := (1 / 1)+x0
  have hx138 : Bounds (7039 / 5120) (3521 / 2560) x138 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx0 <;> norm_num
  let x139 : ℝ := -x0
  have hx139 : Bounds (-961 / 2560) (-1919 / 5120) x139 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x140 : ℝ := (1 / 1)+x139
  have hx140 : Bounds (1599 / 2560) (3201 / 5120) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx139 <;> norm_num
  let x141 : ℝ := (1 / 1)-x0
  have hx141 : Bounds (1599 / 2560) (3201 / 5120) x141 := by
    exact hx140
  let x142 : ℝ := x141⁻¹
  have hx142 : Bounds (1599500156201 / 1000000000000) (1601000625391 / 1000000000000) x142 := by
    apply bounds_inv hx141 <;> norm_num
  let x143 : ℝ := x138*x142
  have hx143 : Bounds (1099500156201 / 500000000000) (1101000625391 / 500000000000) x143 := by
    apply bounds_mul hx138 hx142 <;> norm_num
  let x144 : ℝ := x138/x141
  have hx144 : Bounds (1099500156201 / 500000000000) (1101000625391 / 500000000000) x144 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx143
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (788002853 / 1000000000) (789366607 / 1000000000) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_14.2)
  let x146 : ℝ := (2 / 1)⁻¹
  have hx146 : Bounds (1 / 2) (1 / 2) x146 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x147 : ℝ := x145*x146
  have hx147 : Bounds (788002853 / 2000000000) (789366607 / 2000000000) x147 := by
    apply bounds_mul hx145 hx146 <;> norm_num
  let x148 : ℝ := x145/(2 / 1)
  have hx148 : Bounds (788002853 / 2000000000) (789366607 / 2000000000) x148 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx147
  let x149 : ℝ := (1 / 1)+y
  have hx149 : Bounds (50667 / 40000) (1267099 / 1000000) x149 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x150 : ℝ := -y
  have hx150 : Bounds (-267099 / 1000000) (-10667 / 40000) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (732901 / 1000000) (29333 / 40000) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-y
  have hx152 : Bounds (732901 / 1000000) (29333 / 40000) x152 := by
    exact hx151
  let x153 : ℝ := x152⁻¹
  have hx153 : Bounds (8522824123 / 6250000000) (1364440763487 / 1000000000000) x153 := by
    apply bounds_inv hx152 <;> norm_num
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (5397824123 / 3125000000) (864440763487 / 500000000000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x149/x152
  have hx155 : Bounds (5397824123 / 3125000000) (864440763487 / 500000000000) x155 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx154
  let x156 : ℝ := Real.log x155
  have hx156 : Bounds (34160103 / 62500000) (136868671 / 250000000) x156 := by
    exact bounds_log hx155 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_16.2)
  let x157 : ℝ := (2 / 1)⁻¹
  have hx157 : Bounds (1 / 2) (1 / 2) x157 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x158 : ℝ := x156*x157
  have hx158 : Bounds (34160103 / 125000000) (136868671 / 500000000) x158 := by
    apply bounds_mul hx156 hx157 <;> norm_num
  let x159 : ℝ := x156/(2 / 1)
  have hx159 : Bounds (34160103 / 125000000) (136868671 / 500000000) x159 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx158
  let x160 : ℝ := (1 / 1)+c
  have hx160 : Bounds (1192357 / 1000000) (47707 / 40000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x161 : ℝ := -c
  have hx161 : Bounds (-7707 / 40000) (-192357 / 1000000) x161 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x162 : ℝ := (1 / 1)+x161
  have hx162 : Bounds (32293 / 40000) (807643 / 1000000) x162 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx161 <;> norm_num
  let x163 : ℝ := (1 / 1)-c
  have hx163 : Bounds (32293 / 40000) (807643 / 1000000) x163 := by
    exact hx162
  let x164 : ℝ := x163⁻¹
  have hx164 : Bounds (309542706369 / 250000000000) (1238658532809 / 1000000000000) x164 := by
    apply bounds_inv hx163 <;> norm_num
  let x165 : ℝ := x160*x164
  have hx165 : Bounds (184542706369 / 125000000000) (738658532809 / 500000000000) x165 := by
    apply bounds_mul hx160 hx164 <;> norm_num
  let x166 : ℝ := x160/x163
  have hx166 : Bounds (184542706369 / 125000000000) (738658532809 / 500000000000) x166 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx165
  let x167 : ℝ := Real.log x166
  have hx167 : Bounds (38956717 / 100000000) (7804553 / 20000000) x167 := by
    exact bounds_log hx166 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x168 : ℝ := (2 / 1)⁻¹
  have hx168 : Bounds (1 / 2) (1 / 2) x168 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x169 : ℝ := x167*x168
  have hx169 : Bounds (38956717 / 200000000) (7804553 / 40000000) x169 := by
    apply bounds_mul hx167 hx168 <;> norm_num
  let x170 : ℝ := x167/(2 / 1)
  have hx170 : Bounds (38956717 / 200000000) (7804553 / 40000000) x170 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx169
  let x171 : ℝ := Real.log (2 / 1)
  have hx171 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x171 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x172 : ℝ := c*c
  have hx172 : Bounds (37001215449 / 1000000000000) (59397849 / 1600000000) x172 := by
    apply bounds_mul hc hc <;> norm_num
  let x173 : ℝ := -x172
  have hx173 : Bounds (-59397849 / 1600000000) (-37001215449 / 1000000000000) x173 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx172
  let x174 : ℝ := (1 / 1)+x173
  have hx174 : Bounds (1540602151 / 1600000000) (962998784551 / 1000000000000) x174 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx173 <;> norm_num
  let x175 : ℝ := (1 / 1)-x172
  have hx175 : Bounds (1540602151 / 1600000000) (962998784551 / 1000000000000) x175 := by
    exact hx174
  let x176 : ℝ := Real.log x175
  have hx176 : Bounds (-37830283 / 1000000000) (-37703129 / 1000000000) x176 := by
    exact bounds_log hx175 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (-37830283 / 2000000000) (-37703129 / 2000000000) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (-37830283 / 2000000000) (-37703129 / 2000000000) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (37703129 / 2000000000) (37830283 / 2000000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x171+x180
  have hx181 : Bounds (1423997489 / 2000000000) (284824929 / 400000000) x181 := by
    apply bounds_add hx171 hx180 <;> norm_num
  let x182 : ℝ := x171-x179
  have hx182 : Bounds (1423997489 / 2000000000) (284824929 / 400000000) x182 := by
    exact hx181
  let x183 : ℝ := Real.log (2 / 1)
  have hx183 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x183 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x184 : ℝ := (1 / 1)+(7707 / 40000)
  have hx184 : Bounds (47707 / 40000) (47707 / 40000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((7707 / 40000) : ℝ)) <;> norm_num
  let x185 : ℝ := (1 / 1)+(7707 / 40000)
  have hx185 : Bounds (47707 / 40000) (47707 / 40000) x185 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((7707 / 40000) : ℝ)) <;> norm_num
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (176198683 / 1000000000) (44049671 / 250000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x187 : ℝ := x184*x186
  have hx187 : Bounds (210147764247 / 1000000000000) (656711767 / 3125000000) x187 := by
    apply bounds_mul hx184 hx186 <;> norm_num
  let x188 : ℝ := -(7707 / 40000)
  have hx188 : Bounds (-7707 / 40000) (-7707 / 40000) x188 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((7707 / 40000) : ℝ))
  let x189 : ℝ := (1 / 1)+x188
  have hx189 : Bounds (32293 / 40000) (32293 / 40000) x189 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx188 <;> norm_num
  let x190 : ℝ := (1 / 1)-(7707 / 40000)
  have hx190 : Bounds (32293 / 40000) (32293 / 40000) x190 := by
    exact hx189
  let x191 : ℝ := -(7707 / 40000)
  have hx191 : Bounds (-7707 / 40000) (-7707 / 40000) x191 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((7707 / 40000) : ℝ))
  let x192 : ℝ := (1 / 1)+x191
  have hx192 : Bounds (32293 / 40000) (32293 / 40000) x192 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx191 <;> norm_num
  let x193 : ℝ := (1 / 1)-(7707 / 40000)
  have hx193 : Bounds (32293 / 40000) (32293 / 40000) x193 := by
    exact hx192
  let x194 : ℝ := Real.log x193
  have hx194 : Bounds (-107014483 / 500000000) (-42805793 / 200000000) x194 := by
    exact bounds_log hx193 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x195 : ℝ := x190*x194
  have hx195 : Bounds (-2699858359 / 15625000000) (-21598866771 / 125000000000) x195 := by
    apply bounds_mul hx190 hx194 <;> norm_num
  let x196 : ℝ := x187+x195
  have hx196 : Bounds (37356829271 / 1000000000000) (4669603909 / 125000000000) x196 := by
    apply bounds_add hx187 hx195 <;> norm_num
  let x197 : ℝ := (2 / 1)⁻¹
  have hx197 : Bounds (1 / 2) (1 / 2) x197 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x198 : ℝ := x196*x197
  have hx198 : Bounds (3735682927 / 200000000000) (4669603909 / 250000000000) x198 := by
    apply bounds_mul hx196 hx197 <;> norm_num
  let x199 : ℝ := x196/(2 / 1)
  have hx199 : Bounds (3735682927 / 200000000000) (4669603909 / 250000000000) x199 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx198
  let x200 : ℝ := -x199
  have hx200 : Bounds (-4669603909 / 250000000000) (-3735682927 / 200000000000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx199
  let x201 : ℝ := x183+x200
  have hx201 : Bounds (168617191091 / 250000000000) (134893753273 / 200000000000) x201 := by
    apply bounds_add hx183 hx200 <;> norm_num
  let x202 : ℝ := x183-x199
  have hx202 : Bounds (168617191091 / 250000000000) (134893753273 / 200000000000) x202 := by
    exact hx201
  let x203 : ℝ := biasE (7707 / 40000)
  have hx203 : Bounds (168617191091 / 250000000000) (134893753273 / 200000000000) x203 := by
    simpa +zetaDelta only [biasE, div_one] using hx202
  let x204 : ℝ := Real.log (2 / 1)
  have hx204 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x204 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x205 : ℝ := (1 / 1)+(192357 / 1000000)
  have hx205 : Bounds (1192357 / 1000000) (1192357 / 1000000) x205 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((192357 / 1000000) : ℝ)) <;> norm_num
  let x206 : ℝ := (1 / 1)+(192357 / 1000000)
  have hx206 : Bounds (1192357 / 1000000) (1192357 / 1000000) x206 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((192357 / 1000000) : ℝ)) <;> norm_num
  let x207 : ℝ := Real.log x206
  have hx207 : Bounds (8796601 / 50000000) (175932021 / 1000000000) x207 := by
    exact bounds_log hx206 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x208 : ℝ := x205*x207
  have hx208 : Bounds (209773775571 / 1000000000000) (52443444191 / 250000000000) x208 := by
    apply bounds_mul hx205 hx207 <;> norm_num
  let x209 : ℝ := -(192357 / 1000000)
  have hx209 : Bounds (-192357 / 1000000) (-192357 / 1000000) x209 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((192357 / 1000000) : ℝ))
  let x210 : ℝ := (1 / 1)+x209
  have hx210 : Bounds (807643 / 1000000) (807643 / 1000000) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx209 <;> norm_num
  let x211 : ℝ := (1 / 1)-(192357 / 1000000)
  have hx211 : Bounds (807643 / 1000000) (807643 / 1000000) x211 := by
    exact hx210
  let x212 : ℝ := -(192357 / 1000000)
  have hx212 : Bounds (-192357 / 1000000) (-192357 / 1000000) x212 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((192357 / 1000000) : ℝ))
  let x213 : ℝ := (1 / 1)+x212
  have hx213 : Bounds (807643 / 1000000) (807643 / 1000000) x213 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx212 <;> norm_num
  let x214 : ℝ := (1 / 1)-(192357 / 1000000)
  have hx214 : Bounds (807643 / 1000000) (807643 / 1000000) x214 := by
    exact hx213
  let x215 : ℝ := Real.log x214
  have hx215 : Bounds (-4272703 / 20000000) (-213635149 / 1000000000) x215 := by
    exact bounds_log hx214 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x216 : ℝ := x211*x215
  have hx216 : Bounds (-43135233363 / 250000000000) (-172540932643 / 1000000000000) x216 := by
    apply bounds_mul hx211 hx215 <;> norm_num
  let x217 : ℝ := x208+x216
  have hx217 : Bounds (37232842119 / 1000000000000) (37232844121 / 1000000000000) x217 := by
    apply bounds_add hx208 hx216 <;> norm_num
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (18616421059 / 1000000000000) (18616422061 / 1000000000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (18616421059 / 1000000000000) (18616422061 / 1000000000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := -x220
  have hx221 : Bounds (-18616422061 / 1000000000000) (-18616421059 / 1000000000000) x221 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx220
  let x222 : ℝ := x204+x221
  have hx222 : Bounds (674530757939 / 1000000000000) (674530759941 / 1000000000000) x222 := by
    apply bounds_add hx204 hx221 <;> norm_num
  let x223 : ℝ := x204-x220
  have hx223 : Bounds (674530757939 / 1000000000000) (674530759941 / 1000000000000) x223 := by
    exact hx222
  let x224 : ℝ := biasE (192357 / 1000000)
  have hx224 : Bounds (674530757939 / 1000000000000) (674530759941 / 1000000000000) x224 := by
    simpa +zetaDelta only [biasE, div_one] using hx223
  let x225 : ℝ := biasE c
  have hx225 : Bounds (168617191091 / 250000000000) (674530759941 / 1000000000000) x225 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx203.1 hx224.2
  let x226 : ℝ := x159⁻¹
  have hx226 : Bounds (3653136954913 / 1000000000000) (3659239552059 / 1000000000000) x226 := by
    apply bounds_inv hx159 <;> norm_num
  let x227 : ℝ := x148*x226
  have hx227 : Bounds (287868234287 / 200000000000) (288848150941 / 200000000000) x227 := by
    apply bounds_mul hx148 hx226 <;> norm_num
  let x228 : ℝ := x148/x159
  have hx228 : Bounds (287868234287 / 200000000000) (288848150941 / 200000000000) x228 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx227
  let x229 : ℝ := c*x148
  have hx229 : Bounds (75788932397 / 1000000000000) (38022802751 / 500000000000) x229 := by
    apply bounds_mul hc hx148 <;> norm_num
  let x230 : ℝ := x225+x229
  have hx230 : Bounds (750257696761 / 1000000000000) (750576365443 / 1000000000000) x230 := by
    apply bounds_add hx225 hx229 <;> norm_num
  let x231 : ℝ := x*x170
  have hx231 : Bounds (36502900353 / 1000000000000) (36621950357 / 1000000000000) x231 := by
    apply bounds_mul hx hx170 <;> norm_num
  let x232 : ℝ := x48+x231
  have hx232 : Bounds (693542634957 / 1000000000000) (693777216497 / 1000000000000) x232 := by
    apply bounds_add hx48 hx231 <;> norm_num
  let x233 : ℝ := x232⁻¹
  have hx233 : Bounds (1441384894489 / 1000000000000) (720936211847 / 500000000000) x233 := by
    apply bounds_inv hx232 <;> norm_num
  let x234 : ℝ := x230*x233
  have hx234 : Bounds (216282022217 / 200000000000) (1082235363209 / 1000000000000) x234 := by
    apply bounds_mul hx230 hx233 <;> norm_num
  let x235 : ℝ := x230/x232
  have hx235 : Bounds (216282022217 / 200000000000) (1082235363209 / 1000000000000) x235 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx234
  let x236 : ℝ := y*y
  have hx236 : Bounds (113784889 / 1600000000) (71341875801 / 1000000000000) x236 := by
    apply bounds_mul hy hy <;> norm_num
  let x237 : ℝ := -x236
  have hx237 : Bounds (-71341875801 / 1000000000000) (-113784889 / 1600000000) x237 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx236
  let x238 : ℝ := (1 / 1)+x237
  have hx238 : Bounds (928658124199 / 1000000000000) (1486215111 / 1600000000) x238 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx237 <;> norm_num
  let x239 : ℝ := (1 / 1)-x236
  have hx239 : Bounds (928658124199 / 1000000000000) (1486215111 / 1600000000) x239 := by
    exact hx238
  let x240 : ℝ := x239*x159
  have hx240 : Bounds (50756891479 / 200000000000) (254270358829 / 1000000000000) x240 := by
    apply bounds_mul hx239 hx159 <;> norm_num
  let x241 : ℝ := c*c
  have hx241 : Bounds (37001215449 / 1000000000000) (59397849 / 1600000000) x241 := by
    apply bounds_mul hc hc <;> norm_num
  let x242 : ℝ := -x241
  have hx242 : Bounds (-59397849 / 1600000000) (-37001215449 / 1000000000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx241
  let x243 : ℝ := (1 / 1)+x242
  have hx243 : Bounds (1540602151 / 1600000000) (962998784551 / 1000000000000) x243 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx242 <;> norm_num
  let x244 : ℝ := (1 / 1)-x241
  have hx244 : Bounds (1540602151 / 1600000000) (962998784551 / 1000000000000) x244 := by
    exact hx243
  let x245 : ℝ := x244*x182
  have hx245 : Bounds (685566748303 / 1000000000000) (685715151093 / 1000000000000) x245 := by
    apply bounds_mul hx244 hx182 <;> norm_num
  let x246 : ℝ := y*y
  have hx246 : Bounds (113784889 / 1600000000) (71341875801 / 1000000000000) x246 := by
    apply bounds_mul hy hy <;> norm_num
  let x247 : ℝ := (1 / 1)+x246
  have hx247 : Bounds (1713784889 / 1600000000) (1071341875801 / 1000000000000) x247 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx246 <;> norm_num
  let x248 : ℝ := x247*x159
  have hx248 : Bounds (7317883541 / 25000000000) (18329142341 / 62500000000) x248 := by
    apply bounds_mul hx247 hx159 <;> norm_num
  let x249 : ℝ := -y
  have hx249 : Bounds (-267099 / 1000000) (-10667 / 40000) x249 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x250 : ℝ := x248+x249
  have hx250 : Bounds (640408541 / 25000000000) (1661954841 / 62500000000) x250 := by
    apply bounds_add hx248 hx249 <;> norm_num
  let x251 : ℝ := x248-y
  have hx251 : Bounds (640408541 / 25000000000) (1661954841 / 62500000000) x251 := by
    exact hx250
  let x252 : ℝ := x240*x240
  have hx252 : Bounds (12881310163 / 200000000000) (3232670769 / 50000000000) x252 := by
    apply bounds_mul hx240 hx240 <;> norm_num
  let x253 : ℝ := x252⁻¹
  have hx253 : Bounds (241673234247 / 15625000000) (7763185478387 / 500000000000) x253 := by
    apply bounds_inv hx252 <;> norm_num
  let x254 : ℝ := x251*x253
  have hx254 : Bounds (396210184557 / 1000000000000) (412866037997 / 1000000000000) x254 := by
    apply bounds_mul hx251 hx253 <;> norm_num
  let x255 : ℝ := x251/x252
  have hx255 : Bounds (396210184557 / 1000000000000) (412866037997 / 1000000000000) x255 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx254
  let x256 : ℝ := (-2 / 1)*x255
  have hx256 : Bounds (-412866037997 / 500000000000) (-396210184557 / 500000000000) x256 := by
    apply bounds_mul (bounds_const ((-2 / 1) : ℝ)) hx255 <;> norm_num
  let x257 : ℝ := x256*x228
  have hx257 : Bounds (-596277958309 / 500000000000) (-1140563262349 / 1000000000000) x257 := by
    apply bounds_mul hx256 hx228 <;> norm_num
  let x258 : ℝ := (2 / 1)*x182
  have hx258 : Bounds (1423997489 / 1000000000) (284824929 / 200000000) x258 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx182 <;> norm_num
  let x259 : ℝ := c*c
  have hx259 : Bounds (37001215449 / 1000000000000) (59397849 / 1600000000) x259 := by
    apply bounds_mul hc hc <;> norm_num
  let x260 : ℝ := -x259
  have hx260 : Bounds (-59397849 / 1600000000) (-37001215449 / 1000000000000) x260 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx259
  let x261 : ℝ := x258+x260
  have hx261 : Bounds (11094990667 / 8000000000) (1387123429551 / 1000000000000) x261 := by
    apply bounds_add hx258 hx260 <;> norm_num
  let x262 : ℝ := x258-x259
  have hx262 : Bounds (11094990667 / 8000000000) (1387123429551 / 1000000000000) x262 := by
    exact hx261
  let x263 : ℝ := c*x262
  have hx263 : Bounds (133387444983 / 500000000000) (267264006789 / 1000000000000) x263 := by
    apply bounds_mul hc hx262 <;> norm_num
  let x264 : ℝ := x245*x245
  have hx264 : Bounds (235000883189 / 500000000000) (470205268439 / 1000000000000) x264 := by
    apply bounds_mul hx245 hx245 <;> norm_num
  let x265 : ℝ := x264⁻¹
  have hx265 : Bounds (2126730743191 / 1000000000000) (106382578911 / 50000000000) x265 := by
    apply bounds_inv hx264 <;> norm_num
  let x266 : ℝ := x263*x265
  have hx266 : Bounds (283679180001 / 500000000000) (568644685847 / 1000000000000) x266 := by
    apply bounds_mul hx263 hx265 <;> norm_num
  let x267 : ℝ := x263/x264
  have hx267 : Bounds (283679180001 / 500000000000) (568644685847 / 1000000000000) x267 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx266
  let x268 : ℝ := (2 / 1)*x267
  have hx268 : Bounds (283679180001 / 250000000000) (568644685847 / 500000000000) x268 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx267 <;> norm_num
  let x269 : ℝ := x268*x235
  have hx269 : Bounds (1227094134229 / 1000000000000) (1230814776249 / 1000000000000) x269 := by
    apply bounds_mul hx268 hx235 <;> norm_num
  let x270 : ℝ := x257+x269
  have hx270 : Bounds (34538217611 / 1000000000000) (902515139 / 10000000000) x270 := by
    apply bounds_add hx257 hx269 <;> norm_num
  have hPos : 0 < x270 :=
    lt_of_lt_of_le (by norm_num) hx270.1
  have hBridgeL : doubleCapBridgeL x = x48 := by
    exact hEll'
  rw [← doubleCapBridgeDerivativeTraceForm_eq x]
  simpa +zetaDelta only [doubleCapBridgeDerivativeTraceForm,
    hBridgeL, SmallMean.A, biasB, div_one, pow_two] using hPos

theorem acceptedCell : DoubleCapBridgeDerivativeCellCertificate
    (⟨213, by decide⟩ : Fin 256) doubleCapBridgeDerivativeExpression where
  positive x hx := by
    have hloEq : doubleCapBridgeLo (⟨213, by decide⟩ : Fin 256) =
        (1919 / 10240) := by norm_num [doubleCapBridgeLo, doubleCapBridgeStep]
    have hhiEq : doubleCapBridgeHi (⟨213, by decide⟩ : Fin 256) =
        (961 / 5120) := by norm_num [doubleCapBridgeHi, doubleCapBridgeStep]
    have hlo : (1919 / 10240) ≤ x := by
      simpa only [hloEq] using hx.1
    have hhi : x ≤ (961 / 5120) := by
      simpa only [hhiEq] using hx.2
    exact cell_derivative_pos x ⟨hlo, hhi⟩

#print axioms cell_derivative_pos
#print axioms acceptedCell

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell213

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell214 =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell214
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_derivative_pos (x : ℝ)
    (hx : Bounds (961 / 5120) (385 / 2048) x) :
    0 < doubleCapBridgeDerivativeExpression x := by
  have hxPos0 : 0 < x := by linarith [hx.1]
  have hxHalf : x < 1 / 2 := by linarith [hx.2]
  have hh0 : 0 < doubleCapHighTailFloor x :=
    doubleCapHighTailFloor_pos hxPos0 hxHalf
  have hh1 : doubleCapHighTailFloor x < 1 := by
    have hfloor := doubleCapHighFloor_lt_entropyCap
      (m := (1 - x) / 2) (by linarith) (by linarith)
    have hH1 := H_le_one ((1 - x) / 2)
    unfold doubleCapHighTailFloor
    have heq : 2 * ((1 - x) / 2) - 1 / 2 =
        (1 - 2 * x) / 2 := by ring
    rw [heq] at hfloor
    linarith
  have hEq : biasE (2 * x) = Real.log 2 * H ((1 - 2 * x) / 2) := by
    rw [show 2 * x = 1 - 2 * ((1 - 2 * x) / 2) by ring,
      GeneralCK.Correction.Natural.biasE_probability (by linarith)
        (by linarith), GeneralCK.Certificates.Mixed.hn_eq_H_mul_log]
    ring
  have hEll : Real.log 2 * doubleCapHighTailFloor x =
      (Real.log 2 + biasE (2 * x)) / 2 := by
    dsimp [doubleCapHighTailFloor]
    rw [hEq]
    ring
  let x0 : ℝ := (2 / 1)*x
  have hx0 : Bounds (961 / 2560) (385 / 1024) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx <;> norm_num
  let x1 : ℝ := Real.log (2 / 1)
  have hx1 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x1 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x2 : ℝ := Real.log (2 / 1)
  have hx2 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x2 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x3 : ℝ := (1 / 1)+(385 / 1024)
  have hx3 : Bounds (1409 / 1024) (1409 / 1024) x3 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((385 / 1024) : ℝ)) <;> norm_num
  let x4 : ℝ := (1 / 1)+(385 / 1024)
  have hx4 : Bounds (1409 / 1024) (1409 / 1024) x4 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((385 / 1024) : ℝ)) <;> norm_num
  let x5 : ℝ := Real.log x4
  have hx5 : Bounds (159581853 / 500000000) (319163707 / 1000000000) x5 := by
    exact bounds_log hx4 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x6 : ℝ := x3*x5
  have hx6 : Bounds (27447611191 / 62500000000) (439161780433 / 1000000000000) x6 := by
    apply bounds_mul hx3 hx5 <;> norm_num
  let x7 : ℝ := -(385 / 1024)
  have hx7 : Bounds (-385 / 1024) (-385 / 1024) x7 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((385 / 1024) : ℝ))
  let x8 : ℝ := (1 / 1)+x7
  have hx8 : Bounds (639 / 1024) (639 / 1024) x8 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx7 <;> norm_num
  let x9 : ℝ := (1 / 1)-(385 / 1024)
  have hx9 : Bounds (639 / 1024) (639 / 1024) x9 := by
    exact hx8
  let x10 : ℝ := -(385 / 1024)
  have hx10 : Bounds (-385 / 1024) (-385 / 1024) x10 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((385 / 1024) : ℝ))
  let x11 : ℝ := (1 / 1)+x10
  have hx11 : Bounds (639 / 1024) (639 / 1024) x11 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx10 <;> norm_num
  let x12 : ℝ := (1 / 1)-(385 / 1024)
  have hx12 : Bounds (639 / 1024) (639 / 1024) x12 := by
    exact hx11
  let x13 : ℝ := Real.log x12
  have hx13 : Bounds (-58945919 / 125000000) (-471567351 / 1000000000) x13 := by
    exact bounds_log hx12 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x14 : ℝ := x9*x13
  have hx14 : Bounds (-36783635001 / 125000000000) (-294269079383 / 1000000000000) x14 := by
    apply bounds_mul hx9 hx13 <;> norm_num
  let x15 : ℝ := x6+x14
  have hx15 : Bounds (18111587381 / 125000000000) (2897854021 / 20000000000) x15 := by
    apply bounds_add hx6 hx14 <;> norm_num
  let x16 : ℝ := (2 / 1)⁻¹
  have hx16 : Bounds (1 / 2) (1 / 2) x16 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x17 : ℝ := x15*x16
  have hx17 : Bounds (18111587381 / 250000000000) (2897854021 / 40000000000) x17 := by
    apply bounds_mul hx15 hx16 <;> norm_num
  let x18 : ℝ := x15/(2 / 1)
  have hx18 : Bounds (18111587381 / 250000000000) (2897854021 / 40000000000) x18 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx17
  let x19 : ℝ := -x18
  have hx19 : Bounds (-2897854021 / 40000000000) (-18111587381 / 250000000000) x19 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx18
  let x20 : ℝ := x2+x19
  have hx20 : Bounds (24828033179 / 40000000000) (155175207869 / 250000000000) x20 := by
    apply bounds_add hx2 hx19 <;> norm_num
  let x21 : ℝ := x2-x18
  have hx21 : Bounds (24828033179 / 40000000000) (155175207869 / 250000000000) x21 := by
    exact hx20
  let x22 : ℝ := biasE (385 / 1024)
  have hx22 : Bounds (24828033179 / 40000000000) (155175207869 / 250000000000) x22 := by
    simpa +zetaDelta only [biasE, div_one] using hx21
  let x23 : ℝ := Real.log (2 / 1)
  have hx23 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x23 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x24 : ℝ := (1 / 1)+(961 / 2560)
  have hx24 : Bounds (3521 / 2560) (3521 / 2560) x24 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((961 / 2560) : ℝ)) <;> norm_num
  let x25 : ℝ := (1 / 1)+(961 / 2560)
  have hx25 : Bounds (3521 / 2560) (3521 / 2560) x25 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((961 / 2560) : ℝ)) <;> norm_num
  let x26 : ℝ := Real.log x25
  have hx26 : Bounds (318737781 / 1000000000) (159368891 / 500000000) x26 := by
    exact bounds_log hx25 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x27 : ℝ := x24*x26
  have hx27 : Bounds (21919447791 / 50000000000) (438388957197 / 1000000000000) x27 := by
    apply bounds_mul hx24 hx26 <;> norm_num
  let x28 : ℝ := -(961 / 2560)
  have hx28 : Bounds (-961 / 2560) (-961 / 2560) x28 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((961 / 2560) : ℝ))
  let x29 : ℝ := (1 / 1)+x28
  have hx29 : Bounds (1599 / 2560) (1599 / 2560) x29 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx28 <;> norm_num
  let x30 : ℝ := (1 / 1)-(961 / 2560)
  have hx30 : Bounds (1599 / 2560) (1599 / 2560) x30 := by
    exact hx29
  let x31 : ℝ := -(961 / 2560)
  have hx31 : Bounds (-961 / 2560) (-961 / 2560) x31 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((961 / 2560) : ℝ))
  let x32 : ℝ := (1 / 1)+x31
  have hx32 : Bounds (1599 / 2560) (1599 / 2560) x32 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx31 <;> norm_num
  let x33 : ℝ := (1 / 1)-(961 / 2560)
  have hx33 : Bounds (1599 / 2560) (1599 / 2560) x33 := by
    exact hx32
  let x34 : ℝ := Real.log x33
  have hx34 : Bounds (-18825153 / 40000000) (-58828603 / 125000000) x34 := by
    exact bounds_log hx33 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x35 : ℝ := x30*x34
  have hx35 : Bounds (-293959176241 / 1000000000000) (-58791835123 / 200000000000) x35 := by
    apply bounds_mul hx30 hx34 <;> norm_num
  let x36 : ℝ := x27+x35
  have hx36 : Bounds (144429779579 / 1000000000000) (72214890791 / 500000000000) x36 := by
    apply bounds_add hx27 hx35 <;> norm_num
  let x37 : ℝ := (2 / 1)⁻¹
  have hx37 : Bounds (1 / 2) (1 / 2) x37 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x38 : ℝ := x36*x37
  have hx38 : Bounds (72214889789 / 1000000000000) (72214890791 / 1000000000000) x38 := by
    apply bounds_mul hx36 hx37 <;> norm_num
  let x39 : ℝ := x36/(2 / 1)
  have hx39 : Bounds (72214889789 / 1000000000000) (72214890791 / 1000000000000) x39 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx38
  let x40 : ℝ := -x39
  have hx40 : Bounds (-72214890791 / 1000000000000) (-72214889789 / 1000000000000) x40 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx39
  let x41 : ℝ := x23+x40
  have hx41 : Bounds (620932289209 / 1000000000000) (620932291211 / 1000000000000) x41 := by
    apply bounds_add hx23 hx40 <;> norm_num
  let x42 : ℝ := x23-x39
  have hx42 : Bounds (620932289209 / 1000000000000) (620932291211 / 1000000000000) x42 := by
    exact hx41
  let x43 : ℝ := biasE (961 / 2560)
  have hx43 : Bounds (620932289209 / 1000000000000) (620932291211 / 1000000000000) x43 := by
    simpa +zetaDelta only [biasE, div_one] using hx42
  let x44 : ℝ := biasE x0
  have hx44 : Bounds (24828033179 / 40000000000) (620932291211 / 1000000000000) x44 := by
    exact bounds_biasE hx0 (by norm_num) (by norm_num) hx22.1 hx43.2
  let x45 : ℝ := x1+x44
  have hx45 : Bounds (52553920379 / 40000000000) (1314079472211 / 1000000000000) x45 := by
    apply bounds_add hx1 hx44 <;> norm_num
  let x46 : ℝ := (2 / 1)⁻¹
  have hx46 : Bounds (1 / 2) (1 / 2) x46 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x47 : ℝ := x45*x46
  have hx47 : Bounds (656924004737 / 1000000000000) (328519868053 / 500000000000) x47 := by
    apply bounds_mul hx45 hx46 <;> norm_num
  let x48 : ℝ := x45/(2 / 1)
  have hx48 : Bounds (656924004737 / 1000000000000) (328519868053 / 500000000000) x48 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx47
  let x49 : ℝ := Real.log (2 / 1)
  have hx49 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x49 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x50 : ℝ := (1 / 1)+(133549 / 500000)
  have hx50 : Bounds (633549 / 500000) (633549 / 500000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((133549 / 500000) : ℝ)) <;> norm_num
  let x51 : ℝ := (1 / 1)+(133549 / 500000)
  have hx51 : Bounds (633549 / 500000) (633549 / 500000) x51 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((133549 / 500000) : ℝ)) <;> norm_num
  let x52 : ℝ := Real.log x51
  have hx52 : Bounds (118364623 / 500000000) (236729247 / 1000000000) x52 := by
    exact bounds_log hx51 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x53 : ℝ := x50*x52
  have hx53 : Bounds (74989788537 / 250000000000) (37494894427 / 125000000000) x53 := by
    apply bounds_mul hx50 hx52 <;> norm_num
  let x54 : ℝ := -(133549 / 500000)
  have hx54 : Bounds (-133549 / 500000) (-133549 / 500000) x54 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((133549 / 500000) : ℝ))
  let x55 : ℝ := (1 / 1)+x54
  have hx55 : Bounds (366451 / 500000) (366451 / 500000) x55 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx54 <;> norm_num
  let x56 : ℝ := (1 / 1)-(133549 / 500000)
  have hx56 : Bounds (366451 / 500000) (366451 / 500000) x56 := by
    exact hx55
  let x57 : ℝ := -(133549 / 500000)
  have hx57 : Bounds (-133549 / 500000) (-133549 / 500000) x57 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((133549 / 500000) : ℝ))
  let x58 : ℝ := (1 / 1)+x57
  have hx58 : Bounds (366451 / 500000) (366451 / 500000) x58 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx57 <;> norm_num
  let x59 : ℝ := (1 / 1)-(133549 / 500000)
  have hx59 : Bounds (366451 / 500000) (366451 / 500000) x59 := by
    exact hx58
  let x60 : ℝ := Real.log x59
  have hx60 : Bounds (-77685821 / 250000000) (-310743283 / 1000000000) x60 := by
    exact bounds_log hx59 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x61 : ℝ := x56*x60
  have hx61 : Bounds (-227744374331 / 1000000000000) (-227744373597 / 1000000000000) x61 := by
    apply bounds_mul hx56 hx60 <;> norm_num
  let x62 : ℝ := x53+x61
  have hx62 : Bounds (72214779817 / 1000000000000) (72214781819 / 1000000000000) x62 := by
    apply bounds_add hx53 hx61 <;> norm_num
  let x63 : ℝ := (2 / 1)⁻¹
  have hx63 : Bounds (1 / 2) (1 / 2) x63 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x64 : ℝ := x62*x63
  have hx64 : Bounds (9026847477 / 250000000000) (3610739091 / 100000000000) x64 := by
    apply bounds_mul hx62 hx63 <;> norm_num
  let x65 : ℝ := x62/(2 / 1)
  have hx65 : Bounds (9026847477 / 250000000000) (3610739091 / 100000000000) x65 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx64
  let x66 : ℝ := -x65
  have hx66 : Bounds (-3610739091 / 100000000000) (-9026847477 / 250000000000) x66 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx65
  let x67 : ℝ := x49+x66
  have hx67 : Bounds (65703978909 / 100000000000) (164259947773 / 250000000000) x67 := by
    apply bounds_add hx49 hx66 <;> norm_num
  let x68 : ℝ := x49-x65
  have hx68 : Bounds (65703978909 / 100000000000) (164259947773 / 250000000000) x68 := by
    exact hx67
  let x69 : ℝ := biasE (133549 / 500000)
  have hx69 : Bounds (65703978909 / 100000000000) (164259947773 / 250000000000) x69 := by
    simpa +zetaDelta only [biasE, div_one] using hx68
  let x70 : ℝ := Real.log (2 / 1)
  have hx70 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x70 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x71 : ℝ := (1 / 1)+(267521 / 1000000)
  have hx71 : Bounds (1267521 / 1000000) (1267521 / 1000000) x71 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((267521 / 1000000) : ℝ)) <;> norm_num
  let x72 : ℝ := (1 / 1)+(267521 / 1000000)
  have hx72 : Bounds (1267521 / 1000000) (1267521 / 1000000) x72 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((267521 / 1000000) : ℝ)) <;> norm_num
  let x73 : ℝ := Real.log x72
  have hx73 : Bounds (14816439 / 62500000) (9482521 / 40000000) x73 := by
    exact bounds_log hx72 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x74 : ℝ := x71*x73
  have hx74 : Bounds (300482361243 / 1000000000000) (18780147657 / 62500000000) x74 := by
    apply bounds_mul hx71 hx73 <;> norm_num
  let x75 : ℝ := -(267521 / 1000000)
  have hx75 : Bounds (-267521 / 1000000) (-267521 / 1000000) x75 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((267521 / 1000000) : ℝ))
  let x76 : ℝ := (1 / 1)+x75
  have hx76 : Bounds (732479 / 1000000) (732479 / 1000000) x76 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx75 <;> norm_num
  let x77 : ℝ := (1 / 1)-(267521 / 1000000)
  have hx77 : Bounds (732479 / 1000000) (732479 / 1000000) x77 := by
    exact hx76
  let x78 : ℝ := -(267521 / 1000000)
  have hx78 : Bounds (-267521 / 1000000) (-267521 / 1000000) x78 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((267521 / 1000000) : ℝ))
  let x79 : ℝ := (1 / 1)+x78
  have hx79 : Bounds (732479 / 1000000) (732479 / 1000000) x79 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx78 <;> norm_num
  let x80 : ℝ := (1 / 1)-(267521 / 1000000)
  have hx80 : Bounds (732479 / 1000000) (732479 / 1000000) x80 := by
    exact hx79
  let x81 : ℝ := Real.log x80
  have hx81 : Bounds (-9728769 / 31250000) (-311320607 / 1000000000) x81 := by
    exact bounds_log hx80 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x82 : ℝ := x77*x81
  have hx82 : Bounds (-57008951907 / 250000000000) (-114017903447 / 500000000000) x82 := by
    apply bounds_mul hx77 hx81 <;> norm_num
  let x83 : ℝ := x74+x82
  have hx83 : Bounds (14489310723 / 200000000000) (36223277809 / 500000000000) x83 := by
    apply bounds_add hx74 hx82 <;> norm_num
  let x84 : ℝ := (2 / 1)⁻¹
  have hx84 : Bounds (1 / 2) (1 / 2) x84 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x85 : ℝ := x83*x84
  have hx85 : Bounds (36223276807 / 1000000000000) (36223277809 / 1000000000000) x85 := by
    apply bounds_mul hx83 hx84 <;> norm_num
  let x86 : ℝ := x83/(2 / 1)
  have hx86 : Bounds (36223276807 / 1000000000000) (36223277809 / 1000000000000) x86 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx85
  let x87 : ℝ := -x86
  have hx87 : Bounds (-36223277809 / 1000000000000) (-36223276807 / 1000000000000) x87 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx86
  let x88 : ℝ := x70+x87
  have hx88 : Bounds (656923902191 / 1000000000000) (656923904193 / 1000000000000) x88 := by
    apply bounds_add hx70 hx87 <;> norm_num
  let x89 : ℝ := x70-x86
  have hx89 : Bounds (656923902191 / 1000000000000) (656923904193 / 1000000000000) x89 := by
    exact hx88
  let x90 : ℝ := biasE (267521 / 1000000)
  have hx90 : Bounds (656923902191 / 1000000000000) (656923904193 / 1000000000000) x90 := by
    simpa +zetaDelta only [biasE, div_one] using hx89
  let y : ℝ := doubleCapHighTailY x
  have hEll' : Real.log 2 * doubleCapHighTailFloor x = x48 := by
    simpa +zetaDelta only [div_one] using hEll
  have hy : Bounds (133549 / 500000) (267521 / 1000000) y := by
    dsimp only [y, doubleCapHighTailY]
    apply entropyInverseBias_bracket hh0.le hh1.le
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (267521 / 1000000) ≤ (656923904193 / 1000000000000) := hx90.2
      have h2 : (656924004737 / 1000000000000) ≤ x48 := hx48.1
      linarith [hEll']
    · have h1 : x48 ≤ (328519868053 / 500000000000) := hx48.2
      have h2 : (65703978909 / 100000000000) ≤ biasE (133549 / 500000) := hx69.1
      linarith [hEll']
  let x91 : ℝ := x⁻¹
  have hx91 : Bounds (132987012987 / 25000000000) (5327783558793 / 1000000000000) x91 := by
    apply bounds_inv hx <;> norm_num
  let x92 : ℝ := x48*x91
  have hx92 : Bounds (3494494445977 / 1000000000000) (7001131007 / 2000000000) x92 := by
    apply bounds_mul hx48 hx91 <;> norm_num
  let x93 : ℝ := x48/x
  have hx93 : Bounds (3494494445977 / 1000000000000) (7001131007 / 2000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(96337 / 500000)
  have hx95 : Bounds (596337 / 500000) (596337 / 500000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((96337 / 500000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(96337 / 500000)
  have hx96 : Bounds (596337 / 500000) (596337 / 500000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((96337 / 500000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (35239569 / 200000000) (88098923 / 500000000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (210146588587 / 1000000000000) (210146589781 / 1000000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(96337 / 500000)
  have hx99 : Bounds (-96337 / 500000) (-96337 / 500000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((96337 / 500000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (403663 / 500000) (403663 / 500000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(96337 / 500000)
  have hx101 : Bounds (403663 / 500000) (403663 / 500000) x101 := by
    exact hx100
  let x102 : ℝ := -(96337 / 500000)
  have hx102 : Bounds (-96337 / 500000) (-96337 / 500000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((96337 / 500000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (403663 / 500000) (403663 / 500000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(96337 / 500000)
  have hx104 : Bounds (403663 / 500000) (403663 / 500000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-214027727 / 1000000000) (-107013863 / 500000000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-172790148729 / 1000000000000) (-2159876849 / 12500000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (18678219929 / 500000000000) (37356441861 / 1000000000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (18678219929 / 1000000000000) (18678220931 / 1000000000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (18678219929 / 1000000000000) (18678220931 / 1000000000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-18678220931 / 1000000000000) (-18678219929 / 1000000000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (674468959069 / 1000000000000) (674468961071 / 1000000000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (674468959069 / 1000000000000) (674468961071 / 1000000000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (96337 / 500000)
  have hx114 : Bounds (674468959069 / 1000000000000) (674468961071 / 1000000000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(6031 / 31250)
  have hx116 : Bounds (37281 / 31250) (37281 / 31250) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((6031 / 31250) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(6031 / 31250)
  have hx117 : Bounds (37281 / 31250) (37281 / 31250) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((6031 / 31250) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (176464437 / 1000000000) (88232219 / 500000000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (1684165293 / 8000000000) (210520662819 / 1000000000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(6031 / 31250)
  have hx120 : Bounds (-6031 / 31250) (-6031 / 31250) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((6031 / 31250) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (25219 / 31250) (25219 / 31250) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(6031 / 31250)
  have hx122 : Bounds (25219 / 31250) (25219 / 31250) x122 := by
    exact hx121
  let x123 : ℝ := -(6031 / 31250)
  have hx123 : Bounds (-6031 / 31250) (-6031 / 31250) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((6031 / 31250) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (25219 / 31250) (25219 / 31250) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(6031 / 31250)
  have hx125 : Bounds (25219 / 31250) (25219 / 31250) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-107210849 / 500000000) (-214421697 / 1000000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-8652001283 / 50000000000) (-43260006213 / 250000000000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (7496127193 / 200000000000) (37480637967 / 1000000000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (9370158991 / 500000000000) (2342539873 / 125000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (9370158991 / 500000000000) (2342539873 / 125000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-2342539873 / 125000000000) (-9370158991 / 500000000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (84300857627 / 125000000000) (337203431509 / 500000000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (84300857627 / 125000000000) (337203431509 / 500000000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (6031 / 31250)
  have hx135 : Bounds (84300857627 / 125000000000) (337203431509 / 500000000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(96337 / 500000)
  have hx136 : Bounds (168324555721 / 250000000000) (337233978911 / 500000000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((96337 / 500000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(6031 / 31250)
  have hx137 : Bounds (674409472117 / 1000000000000) (168895284413 / 250000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((6031 / 31250) : ℝ)) <;> norm_num
  let c : ℝ := doubleCapHighTailC x
  have hcMem := Reflection.regularContact_mem
    (x / (Real.log 2 * doubleCapHighTailFloor x))
  have hc0 : 0 ≤ c := by
    dsimp only [c, doubleCapHighTailC]
    apply GeneralCK.Certificates.RegularContactBounds.regularContact_nonneg
    exact div_nonneg hxPos0.le ((mul_pos log_two_pos hh0).le)
  have hcEq : biasE c = x93 * c := by
    have he := doubleCapHighTailC_equation x
    change c = (x / (Real.log 2 * doubleCapHighTailFloor x)) * biasE c at he
    rw [hEll'] at he
    have hxPos : 0 < x := hxPos0
    have hEllPos : 0 < x48 := by rw [← hEll']; exact mul_pos log_two_pos hh0
    change biasE c = (x48 / x) * c
    field_simp [hxPos.ne', hEllPos.ne'] at he ⊢
    nlinarith
  have hc : Bounds (96337 / 500000) (6031 / 31250) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num)
      (by norm_num) (show 0 < x93 by linarith [hx93.1]) hcEq
    · have h1 : x93 * (96337 / 500000) ≤ (337233978911 / 500000000000) := hx136.2
      have h2 : (674468959069 / 1000000000000) ≤ biasE (96337 / 500000) := hx114.1
      linarith
    · have h1 : biasE (6031 / 31250) ≤ (337203431509 / 500000000000) := hx135.2
      have h2 : (674409472117 / 1000000000000) ≤ x93 * (6031 / 31250) := hx137.1
      linarith
  let x138 : ℝ := (1 / 1)+x0
  have hx138 : Bounds (3521 / 2560) (1409 / 1024) x138 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx0 <;> norm_num
  let x139 : ℝ := -x0
  have hx139 : Bounds (-385 / 1024) (-961 / 2560) x139 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x140 : ℝ := (1 / 1)+x139
  have hx140 : Bounds (639 / 1024) (1599 / 2560) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx139 <;> norm_num
  let x141 : ℝ := (1 / 1)-x0
  have hx141 : Bounds (639 / 1024) (1599 / 2560) x141 := by
    exact hx140
  let x142 : ℝ := x141⁻¹
  have hx142 : Bounds (160100062539 / 100000000000) (400625978091 / 250000000000) x142 := by
    apply bounds_inv hx141 <;> norm_num
  let x143 : ℝ := x138*x142
  have hx143 : Bounds (110100062539 / 50000000000) (275625978091 / 125000000000) x143 := by
    apply bounds_mul hx138 hx142 <;> norm_num
  let x144 : ℝ := x138/x141
  have hx144 : Bounds (110100062539 / 50000000000) (275625978091 / 125000000000) x144 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx143
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (157873321 / 200000000) (395365529 / 500000000) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_14.2)
  let x146 : ℝ := (2 / 1)⁻¹
  have hx146 : Bounds (1 / 2) (1 / 2) x146 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x147 : ℝ := x145*x146
  have hx147 : Bounds (157873321 / 400000000) (395365529 / 1000000000) x147 := by
    apply bounds_mul hx145 hx146 <;> norm_num
  let x148 : ℝ := x145/(2 / 1)
  have hx148 : Bounds (157873321 / 400000000) (395365529 / 1000000000) x148 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx147
  let x149 : ℝ := (1 / 1)+y
  have hx149 : Bounds (633549 / 500000) (1267521 / 1000000) x149 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x150 : ℝ := -y
  have hx150 : Bounds (-267521 / 1000000) (-133549 / 500000) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (732479 / 1000000) (366451 / 500000) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-y
  have hx152 : Bounds (732479 / 1000000) (366451 / 500000) x152 := by
    exact hx151
  let x153 : ℝ := x152⁻¹
  have hx153 : Bounds (136443890179 / 100000000000) (1365226852921 / 1000000000000) x153 := by
    apply bounds_inv hx152 <;> norm_num
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (86443890179 / 50000000000) (865226852921 / 500000000000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x149/x152
  have hx155 : Bounds (86443890179 / 50000000000) (865226852921 / 500000000000) x155 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx154
  let x156 : ℝ := Real.log x155
  have hx156 : Bounds (547472529 / 1000000000) (34273977 / 62500000) x156 := by
    exact bounds_log hx155 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_16.2)
  let x157 : ℝ := (2 / 1)⁻¹
  have hx157 : Bounds (1 / 2) (1 / 2) x157 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x158 : ℝ := x156*x157
  have hx158 : Bounds (547472529 / 2000000000) (34273977 / 125000000) x158 := by
    apply bounds_mul hx156 hx157 <;> norm_num
  let x159 : ℝ := x156/(2 / 1)
  have hx159 : Bounds (547472529 / 2000000000) (34273977 / 125000000) x159 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx158
  let x160 : ℝ := (1 / 1)+c
  have hx160 : Bounds (596337 / 500000) (37281 / 31250) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x161 : ℝ := -c
  have hx161 : Bounds (-6031 / 31250) (-96337 / 500000) x161 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x162 : ℝ := (1 / 1)+x161
  have hx162 : Bounds (25219 / 31250) (403663 / 500000) x162 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx161 <;> norm_num
  let x163 : ℝ := (1 / 1)-c
  have hx163 : Bounds (25219 / 31250) (403663 / 500000) x163 := by
    exact hx162
  let x164 : ℝ := x163⁻¹
  have hx164 : Bounds (247731399707 / 200000000000) (1239145089021 / 1000000000000) x164 := by
    apply bounds_inv hx163 <;> norm_num
  let x165 : ℝ := x160*x164
  have hx165 : Bounds (147731399707 / 100000000000) (739145089021 / 500000000000) x165 := by
    apply bounds_mul hx160 hx164 <;> norm_num
  let x166 : ℝ := x160/x163
  have hx166 : Bounds (147731399707 / 100000000000) (739145089021 / 500000000000) x166 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx165
  let x167 : ℝ := Real.log x166
  have hx167 : Bounds (97556393 / 250000000) (78177227 / 200000000) x167 := by
    exact bounds_log hx166 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x168 : ℝ := (2 / 1)⁻¹
  have hx168 : Bounds (1 / 2) (1 / 2) x168 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x169 : ℝ := x167*x168
  have hx169 : Bounds (97556393 / 500000000) (78177227 / 400000000) x169 := by
    apply bounds_mul hx167 hx168 <;> norm_num
  let x170 : ℝ := x167/(2 / 1)
  have hx170 : Bounds (97556393 / 500000000) (78177227 / 400000000) x170 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx169
  let x171 : ℝ := Real.log (2 / 1)
  have hx171 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x171 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x172 : ℝ := c*c
  have hx172 : Bounds (9280817569 / 250000000000) (36372961 / 976562500) x172 := by
    apply bounds_mul hc hc <;> norm_num
  let x173 : ℝ := -x172
  have hx173 : Bounds (-36372961 / 976562500) (-9280817569 / 250000000000) x173 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx172
  let x174 : ℝ := (1 / 1)+x173
  have hx174 : Bounds (940189539 / 976562500) (240719182431 / 250000000000) x174 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx173 <;> norm_num
  let x175 : ℝ := (1 / 1)-x172
  have hx175 : Bounds (940189539 / 976562500) (240719182431 / 250000000000) x175 := by
    exact hx174
  let x176 : ℝ := Real.log x175
  have hx176 : Bounds (-37957261 / 1000000000) (-37829881 / 1000000000) x176 := by
    exact bounds_log hx175 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (-37957261 / 2000000000) (-37829881 / 2000000000) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (-37957261 / 2000000000) (-37829881 / 2000000000) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (37829881 / 2000000000) (37957261 / 2000000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x171+x180
  have hx181 : Bounds (1424124241 / 2000000000) (1424251623 / 2000000000) x181 := by
    apply bounds_add hx171 hx180 <;> norm_num
  let x182 : ℝ := x171-x179
  have hx182 : Bounds (1424124241 / 2000000000) (1424251623 / 2000000000) x182 := by
    exact hx181
  let x183 : ℝ := Real.log (2 / 1)
  have hx183 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x183 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x184 : ℝ := (1 / 1)+(6031 / 31250)
  have hx184 : Bounds (37281 / 31250) (37281 / 31250) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((6031 / 31250) : ℝ)) <;> norm_num
  let x185 : ℝ := (1 / 1)+(6031 / 31250)
  have hx185 : Bounds (37281 / 31250) (37281 / 31250) x185 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((6031 / 31250) : ℝ)) <;> norm_num
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (176464437 / 1000000000) (88232219 / 500000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x187 : ℝ := x184*x186
  have hx187 : Bounds (1684165293 / 8000000000) (210520662819 / 1000000000000) x187 := by
    apply bounds_mul hx184 hx186 <;> norm_num
  let x188 : ℝ := -(6031 / 31250)
  have hx188 : Bounds (-6031 / 31250) (-6031 / 31250) x188 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((6031 / 31250) : ℝ))
  let x189 : ℝ := (1 / 1)+x188
  have hx189 : Bounds (25219 / 31250) (25219 / 31250) x189 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx188 <;> norm_num
  let x190 : ℝ := (1 / 1)-(6031 / 31250)
  have hx190 : Bounds (25219 / 31250) (25219 / 31250) x190 := by
    exact hx189
  let x191 : ℝ := -(6031 / 31250)
  have hx191 : Bounds (-6031 / 31250) (-6031 / 31250) x191 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((6031 / 31250) : ℝ))
  let x192 : ℝ := (1 / 1)+x191
  have hx192 : Bounds (25219 / 31250) (25219 / 31250) x192 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx191 <;> norm_num
  let x193 : ℝ := (1 / 1)-(6031 / 31250)
  have hx193 : Bounds (25219 / 31250) (25219 / 31250) x193 := by
    exact hx192
  let x194 : ℝ := Real.log x193
  have hx194 : Bounds (-107210849 / 500000000) (-214421697 / 1000000000) x194 := by
    exact bounds_log hx193 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x195 : ℝ := x190*x194
  have hx195 : Bounds (-8652001283 / 50000000000) (-43260006213 / 250000000000) x195 := by
    apply bounds_mul hx190 hx194 <;> norm_num
  let x196 : ℝ := x187+x195
  have hx196 : Bounds (7496127193 / 200000000000) (37480637967 / 1000000000000) x196 := by
    apply bounds_add hx187 hx195 <;> norm_num
  let x197 : ℝ := (2 / 1)⁻¹
  have hx197 : Bounds (1 / 2) (1 / 2) x197 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x198 : ℝ := x196*x197
  have hx198 : Bounds (9370158991 / 500000000000) (2342539873 / 125000000000) x198 := by
    apply bounds_mul hx196 hx197 <;> norm_num
  let x199 : ℝ := x196/(2 / 1)
  have hx199 : Bounds (9370158991 / 500000000000) (2342539873 / 125000000000) x199 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx198
  let x200 : ℝ := -x199
  have hx200 : Bounds (-2342539873 / 125000000000) (-9370158991 / 500000000000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx199
  let x201 : ℝ := x183+x200
  have hx201 : Bounds (84300857627 / 125000000000) (337203431509 / 500000000000) x201 := by
    apply bounds_add hx183 hx200 <;> norm_num
  let x202 : ℝ := x183-x199
  have hx202 : Bounds (84300857627 / 125000000000) (337203431509 / 500000000000) x202 := by
    exact hx201
  let x203 : ℝ := biasE (6031 / 31250)
  have hx203 : Bounds (84300857627 / 125000000000) (337203431509 / 500000000000) x203 := by
    simpa +zetaDelta only [biasE, div_one] using hx202
  let x204 : ℝ := Real.log (2 / 1)
  have hx204 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x204 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x205 : ℝ := (1 / 1)+(96337 / 500000)
  have hx205 : Bounds (596337 / 500000) (596337 / 500000) x205 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((96337 / 500000) : ℝ)) <;> norm_num
  let x206 : ℝ := (1 / 1)+(96337 / 500000)
  have hx206 : Bounds (596337 / 500000) (596337 / 500000) x206 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((96337 / 500000) : ℝ)) <;> norm_num
  let x207 : ℝ := Real.log x206
  have hx207 : Bounds (35239569 / 200000000) (88098923 / 500000000) x207 := by
    exact bounds_log hx206 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x208 : ℝ := x205*x207
  have hx208 : Bounds (210146588587 / 1000000000000) (210146589781 / 1000000000000) x208 := by
    apply bounds_mul hx205 hx207 <;> norm_num
  let x209 : ℝ := -(96337 / 500000)
  have hx209 : Bounds (-96337 / 500000) (-96337 / 500000) x209 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((96337 / 500000) : ℝ))
  let x210 : ℝ := (1 / 1)+x209
  have hx210 : Bounds (403663 / 500000) (403663 / 500000) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx209 <;> norm_num
  let x211 : ℝ := (1 / 1)-(96337 / 500000)
  have hx211 : Bounds (403663 / 500000) (403663 / 500000) x211 := by
    exact hx210
  let x212 : ℝ := -(96337 / 500000)
  have hx212 : Bounds (-96337 / 500000) (-96337 / 500000) x212 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((96337 / 500000) : ℝ))
  let x213 : ℝ := (1 / 1)+x212
  have hx213 : Bounds (403663 / 500000) (403663 / 500000) x213 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx212 <;> norm_num
  let x214 : ℝ := (1 / 1)-(96337 / 500000)
  have hx214 : Bounds (403663 / 500000) (403663 / 500000) x214 := by
    exact hx213
  let x215 : ℝ := Real.log x214
  have hx215 : Bounds (-214027727 / 1000000000) (-107013863 / 500000000) x215 := by
    exact bounds_log hx214 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x216 : ℝ := x211*x215
  have hx216 : Bounds (-172790148729 / 1000000000000) (-2159876849 / 12500000000) x216 := by
    apply bounds_mul hx211 hx215 <;> norm_num
  let x217 : ℝ := x208+x216
  have hx217 : Bounds (18678219929 / 500000000000) (37356441861 / 1000000000000) x217 := by
    apply bounds_add hx208 hx216 <;> norm_num
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (18678219929 / 1000000000000) (18678220931 / 1000000000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (18678219929 / 1000000000000) (18678220931 / 1000000000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := -x220
  have hx221 : Bounds (-18678220931 / 1000000000000) (-18678219929 / 1000000000000) x221 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx220
  let x222 : ℝ := x204+x221
  have hx222 : Bounds (674468959069 / 1000000000000) (674468961071 / 1000000000000) x222 := by
    apply bounds_add hx204 hx221 <;> norm_num
  let x223 : ℝ := x204-x220
  have hx223 : Bounds (674468959069 / 1000000000000) (674468961071 / 1000000000000) x223 := by
    exact hx222
  let x224 : ℝ := biasE (96337 / 500000)
  have hx224 : Bounds (674468959069 / 1000000000000) (674468961071 / 1000000000000) x224 := by
    simpa +zetaDelta only [biasE, div_one] using hx223
  let x225 : ℝ := biasE c
  have hx225 : Bounds (84300857627 / 125000000000) (674468961071 / 1000000000000) x225 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx203.1 hx224.2
  let x226 : ℝ := x159⁻¹
  have hx226 : Bounds (3647081866221 / 1000000000000) (3653151334649 / 1000000000000) x226 := by
    apply bounds_inv hx159 <;> norm_num
  let x227 : ℝ := x148*x226
  have hx227 : Bounds (1439442315447 / 1000000000000) (1444330109941 / 1000000000000) x227 := by
    apply bounds_mul hx148 hx226 <;> norm_num
  let x228 : ℝ := x148/x159
  have hx228 : Bounds (1439442315447 / 1000000000000) (1444330109941 / 1000000000000) x228 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx227
  let x229 : ℝ := c*x148
  have hx229 : Bounds (121672337 / 1600000000) (76302384173 / 1000000000000) x229 := by
    apply bounds_mul hc hx148 <;> norm_num
  let x230 : ℝ := x225+x229
  have hx230 : Bounds (750452071641 / 1000000000000) (187692836311 / 250000000000) x230 := by
    apply bounds_add hx225 hx229 <;> norm_num
  let x231 : ℝ := x*x170
  have hx231 : Bounds (36621755341 / 1000000000000) (18370503171 / 500000000000) x231 := by
    apply bounds_mul hx hx170 <;> norm_num
  let x232 : ℝ := x48+x231
  have hx232 : Bounds (346772880039 / 500000000000) (43361296403 / 62500000000) x232 := by
    apply bounds_add hx48 hx231 <;> norm_num
  let x233 : ℝ := x232⁻¹
  have hx233 : Bounds (288275513809 / 200000000000) (1441865926609 / 1000000000000) x233 := by
    apply bounds_inv hx232 <;> norm_num
  let x234 : ℝ := x230*x233
  have hx234 : Bounds (540842391353 / 500000000000) (541255810691 / 500000000000) x234 := by
    apply bounds_mul hx230 hx233 <;> norm_num
  let x235 : ℝ := x230/x232
  have hx235 : Bounds (540842391353 / 500000000000) (541255810691 / 500000000000) x235 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx234
  let x236 : ℝ := y*y
  have hx236 : Bounds (17835335401 / 250000000000) (71567485441 / 1000000000000) x236 := by
    apply bounds_mul hy hy <;> norm_num
  let x237 : ℝ := -x236
  have hx237 : Bounds (-71567485441 / 1000000000000) (-17835335401 / 250000000000) x237 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx236
  let x238 : ℝ := (1 / 1)+x237
  have hx238 : Bounds (928432514559 / 1000000000000) (232164664599 / 250000000000) x238 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx237 <;> norm_num
  let x239 : ℝ := (1 / 1)-x236
  have hx239 : Bounds (928432514559 / 1000000000000) (232164664599 / 250000000000) x239 := by
    exact hx238
  let x240 : ℝ := x239*x159
  have hx240 : Bounds (2033165187 / 8000000000) (25463060399 / 100000000000) x240 := by
    apply bounds_mul hx239 hx159 <;> norm_num
  let x241 : ℝ := c*c
  have hx241 : Bounds (9280817569 / 250000000000) (36372961 / 976562500) x241 := by
    apply bounds_mul hc hc <;> norm_num
  let x242 : ℝ := -x241
  have hx242 : Bounds (-36372961 / 976562500) (-9280817569 / 250000000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx241
  let x243 : ℝ := (1 / 1)+x242
  have hx243 : Bounds (940189539 / 976562500) (240719182431 / 250000000000) x243 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx242 <;> norm_num
  let x244 : ℝ := (1 / 1)-x241
  have hx244 : Bounds (940189539 / 976562500) (240719182431 / 250000000000) x244 := by
    exact hx243
  let x245 : ℝ := x244*x182
  have hx245 : Bounds (5484325739 / 8000000000) (68568937253 / 100000000000) x245 := by
    apply bounds_mul hx244 hx182 <;> norm_num
  let x246 : ℝ := y*y
  have hx246 : Bounds (17835335401 / 250000000000) (71567485441 / 1000000000000) x246 := by
    apply bounds_mul hy hy <;> norm_num
  let x247 : ℝ := (1 / 1)+x246
  have hx247 : Bounds (267835335401 / 250000000000) (1071567485441 / 1000000000000) x247 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx246 <;> norm_num
  let x248 : ℝ := x247*x159
  have hx248 : Bounds (58652995371 / 200000000000) (734537587 / 2500000000) x248 := by
    apply bounds_mul hx247 hx159 <;> norm_num
  let x249 : ℝ := -y
  have hx249 : Bounds (-267521 / 1000000) (-133549 / 500000) x249 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x250 : ℝ := x248+x249
  have hx250 : Bounds (5148795371 / 200000000000) (66792587 / 2500000000) x250 := by
    apply bounds_add hx248 hx249 <;> norm_num
  let x251 : ℝ := x248-y
  have hx251 : Bounds (5148795371 / 200000000000) (66792587 / 2500000000) x251 := by
    exact hx250
  let x252 : ℝ := x240*x240
  have hx252 : Bounds (64590010587 / 1000000000000) (64836744489 / 1000000000000) x252 := by
    apply bounds_mul hx240 hx240 <;> norm_num
  let x253 : ℝ := x252⁻¹
  have hx253 : Bounds (3084670607327 / 200000000000) (483820945623 / 31250000000) x253 := by
    apply bounds_inv hx252 <;> norm_num
  let x254 : ℝ := x251*x253
  have hx254 : Bounds (397058443601 / 1000000000000) (206820176659 / 500000000000) x254 := by
    apply bounds_mul hx251 hx253 <;> norm_num
  let x255 : ℝ := x251/x252
  have hx255 : Bounds (397058443601 / 1000000000000) (206820176659 / 500000000000) x255 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx254
  let x256 : ℝ := (-2 / 1)*x255
  have hx256 : Bounds (-206820176659 / 250000000000) (-397058443601 / 500000000000) x256 := by
    apply bounds_mul (bounds_const ((-2 / 1) : ℝ)) hx255 <;> norm_num
  let x257 : ℝ := x256*x228
  have hx257 : Bounds (-74679152123 / 62500000000) (-1143085450849 / 1000000000000) x257 := by
    apply bounds_mul hx256 hx228 <;> norm_num
  let x258 : ℝ := (2 / 1)*x182
  have hx258 : Bounds (1424124241 / 1000000000) (1424251623 / 1000000000) x258 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx182 <;> norm_num
  let x259 : ℝ := c*c
  have hx259 : Bounds (9280817569 / 250000000000) (36372961 / 976562500) x259 := by
    apply bounds_mul hc hc <;> norm_num
  let x260 : ℝ := -x259
  have hx260 : Bounds (-36372961 / 976562500) (-9280817569 / 250000000000) x260 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx259
  let x261 : ℝ := x258+x260
  have hx261 : Bounds (173359791117 / 125000000000) (346782088181 / 250000000000) x261 := by
    apply bounds_add hx258 hx260 <;> norm_num
  let x262 : ℝ := x258-x259
  have hx262 : Bounds (173359791117 / 125000000000) (346782088181 / 250000000000) x262 := by
    exact hx261
  let x263 : ℝ := c*x262
  have hx263 : Bounds (267215395149 / 1000000000000) (267704675049 / 1000000000000) x263 := by
    apply bounds_mul hc hx262 <;> norm_num
  let x264 : ℝ := x245*x245
  have hx264 : Bounds (469966075179 / 1000000000000) (470169915601 / 1000000000000) x264 := by
    apply bounds_mul hx245 hx245 <;> norm_num
  let x265 : ℝ := x264⁻¹
  have hx265 : Bounds (2126890655523 / 1000000000000) (2127813161023 / 1000000000000) x265 := by
    apply bounds_inv hx264 <;> norm_num
  let x266 : ℝ := x263*x265
  have hx266 : Bounds (284168963477 / 500000000000) (569625530837 / 1000000000000) x266 := by
    apply bounds_mul hx263 hx265 <;> norm_num
  let x267 : ℝ := x263/x264
  have hx267 : Bounds (284168963477 / 500000000000) (569625530837 / 1000000000000) x267 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx266
  let x268 : ℝ := (2 / 1)*x267
  have hx268 : Bounds (284168963477 / 250000000000) (569625530837 / 500000000000) x268 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx267 <;> norm_num
  let x269 : ℝ := x268*x235
  have hx269 : Bounds (1229524974041 / 1000000000000) (616626256967 / 500000000000) x269 := by
    apply bounds_mul hx268 hx235 <;> norm_num
  let x270 : ℝ := x257+x269
  have hx270 : Bounds (34658540073 / 1000000000000) (18033412617 / 200000000000) x270 := by
    apply bounds_add hx257 hx269 <;> norm_num
  have hPos : 0 < x270 :=
    lt_of_lt_of_le (by norm_num) hx270.1
  have hBridgeL : doubleCapBridgeL x = x48 := by
    exact hEll'
  rw [← doubleCapBridgeDerivativeTraceForm_eq x]
  simpa +zetaDelta only [doubleCapBridgeDerivativeTraceForm,
    hBridgeL, SmallMean.A, biasB, div_one, pow_two] using hPos

theorem acceptedCell : DoubleCapBridgeDerivativeCellCertificate
    (⟨214, by decide⟩ : Fin 256) doubleCapBridgeDerivativeExpression where
  positive x hx := by
    have hloEq : doubleCapBridgeLo (⟨214, by decide⟩ : Fin 256) =
        (961 / 5120) := by norm_num [doubleCapBridgeLo, doubleCapBridgeStep]
    have hhiEq : doubleCapBridgeHi (⟨214, by decide⟩ : Fin 256) =
        (385 / 2048) := by norm_num [doubleCapBridgeHi, doubleCapBridgeStep]
    have hlo : (961 / 5120) ≤ x := by
      simpa only [hloEq] using hx.1
    have hhi : x ≤ (385 / 2048) := by
      simpa only [hhiEq] using hx.2
    exact cell_derivative_pos x ⟨hlo, hhi⟩

#print axioms cell_derivative_pos
#print axioms acceptedCell

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell214

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell215 =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell215
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_derivative_pos (x : ℝ)
    (hx : Bounds (385 / 2048) (241 / 1280) x) :
    0 < doubleCapBridgeDerivativeExpression x := by
  have hxPos0 : 0 < x := by linarith [hx.1]
  have hxHalf : x < 1 / 2 := by linarith [hx.2]
  have hh0 : 0 < doubleCapHighTailFloor x :=
    doubleCapHighTailFloor_pos hxPos0 hxHalf
  have hh1 : doubleCapHighTailFloor x < 1 := by
    have hfloor := doubleCapHighFloor_lt_entropyCap
      (m := (1 - x) / 2) (by linarith) (by linarith)
    have hH1 := H_le_one ((1 - x) / 2)
    unfold doubleCapHighTailFloor
    have heq : 2 * ((1 - x) / 2) - 1 / 2 =
        (1 - 2 * x) / 2 := by ring
    rw [heq] at hfloor
    linarith
  have hEq : biasE (2 * x) = Real.log 2 * H ((1 - 2 * x) / 2) := by
    rw [show 2 * x = 1 - 2 * ((1 - 2 * x) / 2) by ring,
      GeneralCK.Correction.Natural.biasE_probability (by linarith)
        (by linarith), GeneralCK.Certificates.Mixed.hn_eq_H_mul_log]
    ring
  have hEll : Real.log 2 * doubleCapHighTailFloor x =
      (Real.log 2 + biasE (2 * x)) / 2 := by
    dsimp [doubleCapHighTailFloor]
    rw [hEq]
    ring
  let x0 : ℝ := (2 / 1)*x
  have hx0 : Bounds (385 / 1024) (241 / 640) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx <;> norm_num
  let x1 : ℝ := Real.log (2 / 1)
  have hx1 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x1 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x2 : ℝ := Real.log (2 / 1)
  have hx2 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x2 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x3 : ℝ := (1 / 1)+(241 / 640)
  have hx3 : Bounds (881 / 640) (881 / 640) x3 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((241 / 640) : ℝ)) <;> norm_num
  let x4 : ℝ := (1 / 1)+(241 / 640)
  have hx4 : Bounds (881 / 640) (881 / 640) x4 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((241 / 640) : ℝ)) <;> norm_num
  let x5 : ℝ := Real.log x4
  have hx5 : Bounds (319589449 / 1000000000) (6391789 / 20000000) x5 := by
    exact bounds_log hx4 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x6 : ℝ := x3*x5
  have hx6 : Bounds (439934850889 / 1000000000000) (219967426133 / 500000000000) x6 := by
    apply bounds_mul hx3 hx5 <;> norm_num
  let x7 : ℝ := -(241 / 640)
  have hx7 : Bounds (-241 / 640) (-241 / 640) x7 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((241 / 640) : ℝ))
  let x8 : ℝ := (1 / 1)+x7
  have hx8 : Bounds (399 / 640) (399 / 640) x8 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx7 <;> norm_num
  let x9 : ℝ := (1 / 1)-(241 / 640)
  have hx9 : Bounds (399 / 640) (399 / 640) x9 := by
    exact hx8
  let x10 : ℝ := -(241 / 640)
  have hx10 : Bounds (-241 / 640) (-241 / 640) x10 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((241 / 640) : ℝ))
  let x11 : ℝ := (1 / 1)+x10
  have hx11 : Bounds (399 / 640) (399 / 640) x11 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx10 <;> norm_num
  let x12 : ℝ := (1 / 1)-(241 / 640)
  have hx12 : Bounds (399 / 640) (399 / 640) x12 := by
    exact hx11
  let x13 : ℝ := Real.log x12
  have hx13 : Bounds (-11812669 / 25000000) (-472506759 / 1000000000) x13 := by
    exact bounds_log hx12 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x14 : ℝ := x9*x13
  have hx14 : Bounds (-73644608297 / 250000000000) (-73644608141 / 250000000000) x14 := by
    apply bounds_mul hx9 hx13 <;> norm_num
  let x15 : ℝ := x6+x14
  have hx15 : Bounds (145356417701 / 1000000000000) (72678209851 / 500000000000) x15 := by
    apply bounds_add hx6 hx14 <;> norm_num
  let x16 : ℝ := (2 / 1)⁻¹
  have hx16 : Bounds (1 / 2) (1 / 2) x16 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x17 : ℝ := x15*x16
  have hx17 : Bounds (1453564177 / 20000000000) (72678209851 / 1000000000000) x17 := by
    apply bounds_mul hx15 hx16 <;> norm_num
  let x18 : ℝ := x15/(2 / 1)
  have hx18 : Bounds (1453564177 / 20000000000) (72678209851 / 1000000000000) x18 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx17
  let x19 : ℝ := -x18
  have hx19 : Bounds (-72678209851 / 1000000000000) (-1453564177 / 20000000000) x19 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx18
  let x20 : ℝ := x2+x19
  have hx20 : Bounds (620468970149 / 1000000000000) (12409379443 / 20000000000) x20 := by
    apply bounds_add hx2 hx19 <;> norm_num
  let x21 : ℝ := x2-x18
  have hx21 : Bounds (620468970149 / 1000000000000) (12409379443 / 20000000000) x21 := by
    exact hx20
  let x22 : ℝ := biasE (241 / 640)
  have hx22 : Bounds (620468970149 / 1000000000000) (12409379443 / 20000000000) x22 := by
    simpa +zetaDelta only [biasE, div_one] using hx21
  let x23 : ℝ := Real.log (2 / 1)
  have hx23 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x23 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x24 : ℝ := (1 / 1)+(385 / 1024)
  have hx24 : Bounds (1409 / 1024) (1409 / 1024) x24 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((385 / 1024) : ℝ)) <;> norm_num
  let x25 : ℝ := (1 / 1)+(385 / 1024)
  have hx25 : Bounds (1409 / 1024) (1409 / 1024) x25 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((385 / 1024) : ℝ)) <;> norm_num
  let x26 : ℝ := Real.log x25
  have hx26 : Bounds (159581853 / 500000000) (319163707 / 1000000000) x26 := by
    exact bounds_log hx25 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x27 : ℝ := x24*x26
  have hx27 : Bounds (27447611191 / 62500000000) (439161780433 / 1000000000000) x27 := by
    apply bounds_mul hx24 hx26 <;> norm_num
  let x28 : ℝ := -(385 / 1024)
  have hx28 : Bounds (-385 / 1024) (-385 / 1024) x28 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((385 / 1024) : ℝ))
  let x29 : ℝ := (1 / 1)+x28
  have hx29 : Bounds (639 / 1024) (639 / 1024) x29 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx28 <;> norm_num
  let x30 : ℝ := (1 / 1)-(385 / 1024)
  have hx30 : Bounds (639 / 1024) (639 / 1024) x30 := by
    exact hx29
  let x31 : ℝ := -(385 / 1024)
  have hx31 : Bounds (-385 / 1024) (-385 / 1024) x31 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((385 / 1024) : ℝ))
  let x32 : ℝ := (1 / 1)+x31
  have hx32 : Bounds (639 / 1024) (639 / 1024) x32 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx31 <;> norm_num
  let x33 : ℝ := (1 / 1)-(385 / 1024)
  have hx33 : Bounds (639 / 1024) (639 / 1024) x33 := by
    exact hx32
  let x34 : ℝ := Real.log x33
  have hx34 : Bounds (-58945919 / 125000000) (-471567351 / 1000000000) x34 := by
    exact bounds_log hx33 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x35 : ℝ := x30*x34
  have hx35 : Bounds (-36783635001 / 125000000000) (-294269079383 / 1000000000000) x35 := by
    apply bounds_mul hx30 hx34 <;> norm_num
  let x36 : ℝ := x27+x35
  have hx36 : Bounds (18111587381 / 125000000000) (2897854021 / 20000000000) x36 := by
    apply bounds_add hx27 hx35 <;> norm_num
  let x37 : ℝ := (2 / 1)⁻¹
  have hx37 : Bounds (1 / 2) (1 / 2) x37 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x38 : ℝ := x36*x37
  have hx38 : Bounds (18111587381 / 250000000000) (2897854021 / 40000000000) x38 := by
    apply bounds_mul hx36 hx37 <;> norm_num
  let x39 : ℝ := x36/(2 / 1)
  have hx39 : Bounds (18111587381 / 250000000000) (2897854021 / 40000000000) x39 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx38
  let x40 : ℝ := -x39
  have hx40 : Bounds (-2897854021 / 40000000000) (-18111587381 / 250000000000) x40 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx39
  let x41 : ℝ := x23+x40
  have hx41 : Bounds (24828033179 / 40000000000) (155175207869 / 250000000000) x41 := by
    apply bounds_add hx23 hx40 <;> norm_num
  let x42 : ℝ := x23-x39
  have hx42 : Bounds (24828033179 / 40000000000) (155175207869 / 250000000000) x42 := by
    exact hx41
  let x43 : ℝ := biasE (385 / 1024)
  have hx43 : Bounds (24828033179 / 40000000000) (155175207869 / 250000000000) x43 := by
    simpa +zetaDelta only [biasE, div_one] using hx42
  let x44 : ℝ := biasE x0
  have hx44 : Bounds (620468970149 / 1000000000000) (155175207869 / 250000000000) x44 := by
    exact bounds_biasE hx0 (by norm_num) (by norm_num) hx22.1 hx43.2
  let x45 : ℝ := x1+x44
  have hx45 : Bounds (1313616150149 / 1000000000000) (328462003119 / 250000000000) x45 := by
    apply bounds_add hx1 hx44 <;> norm_num
  let x46 : ℝ := (2 / 1)⁻¹
  have hx46 : Bounds (1 / 2) (1 / 2) x46 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x47 : ℝ := x45*x46
  have hx47 : Bounds (328404037537 / 500000000000) (328462003119 / 500000000000) x47 := by
    apply bounds_mul hx45 hx46 <;> norm_num
  let x48 : ℝ := x45/(2 / 1)
  have hx48 : Bounds (328404037537 / 500000000000) (328462003119 / 500000000000) x48 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx47
  let x49 : ℝ := Real.log (2 / 1)
  have hx49 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x49 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x50 : ℝ := (1 / 1)+(836 / 3125)
  have hx50 : Bounds (3961 / 3125) (3961 / 3125) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((836 / 3125) : ℝ)) <;> norm_num
  let x51 : ℝ := (1 / 1)+(836 / 3125)
  have hx51 : Bounds (3961 / 3125) (3961 / 3125) x51 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((836 / 3125) : ℝ)) <;> norm_num
  let x52 : ℝ := Real.log x51
  have hx52 : Bounds (47412447 / 200000000) (59265559 / 250000000) x52 := by
    exact bounds_log hx51 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x53 : ℝ := x50*x52
  have hx53 : Bounds (300481124107 / 1000000000000) (2403849003 / 8000000000) x53 := by
    apply bounds_mul hx50 hx52 <;> norm_num
  let x54 : ℝ := -(836 / 3125)
  have hx54 : Bounds (-836 / 3125) (-836 / 3125) x54 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((836 / 3125) : ℝ))
  let x55 : ℝ := (1 / 1)+x54
  have hx55 : Bounds (2289 / 3125) (2289 / 3125) x55 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx54 <;> norm_num
  let x56 : ℝ := (1 / 1)-(836 / 3125)
  have hx56 : Bounds (2289 / 3125) (2289 / 3125) x56 := by
    exact hx55
  let x57 : ℝ := -(836 / 3125)
  have hx57 : Bounds (-836 / 3125) (-836 / 3125) x57 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((836 / 3125) : ℝ))
  let x58 : ℝ := (1 / 1)+x57
  have hx58 : Bounds (2289 / 3125) (2289 / 3125) x58 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx57 <;> norm_num
  let x59 : ℝ := (1 / 1)-(836 / 3125)
  have hx59 : Bounds (2289 / 3125) (2289 / 3125) x59 := by
    exact hx58
  let x60 : ℝ := Real.log x59
  have hx60 : Bounds (-311319243 / 1000000000) (-155659621 / 500000000) x60 := by
    exact bounds_log hx59 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x61 : ℝ := x56*x60
  have hx61 : Bounds (-228035119113 / 1000000000000) (-11401755919 / 50000000000) x61 := by
    apply bounds_mul hx56 hx60 <;> norm_num
  let x62 : ℝ := x53+x61
  have hx62 : Bounds (36223002497 / 500000000000) (14489201399 / 200000000000) x62 := by
    apply bounds_add hx53 hx61 <;> norm_num
  let x63 : ℝ := (2 / 1)⁻¹
  have hx63 : Bounds (1 / 2) (1 / 2) x63 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x64 : ℝ := x62*x63
  have hx64 : Bounds (36223002497 / 1000000000000) (18111501749 / 500000000000) x64 := by
    apply bounds_mul hx62 hx63 <;> norm_num
  let x65 : ℝ := x62/(2 / 1)
  have hx65 : Bounds (36223002497 / 1000000000000) (18111501749 / 500000000000) x65 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx64
  let x66 : ℝ := -x65
  have hx66 : Bounds (-18111501749 / 500000000000) (-36223002497 / 1000000000000) x66 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx65
  let x67 : ℝ := x49+x66
  have hx67 : Bounds (328462088251 / 500000000000) (656924178503 / 1000000000000) x67 := by
    apply bounds_add hx49 hx66 <;> norm_num
  let x68 : ℝ := x49-x65
  have hx68 : Bounds (328462088251 / 500000000000) (656924178503 / 1000000000000) x68 := by
    exact hx67
  let x69 : ℝ := biasE (836 / 3125)
  have hx69 : Bounds (328462088251 / 500000000000) (656924178503 / 1000000000000) x69 := by
    simpa +zetaDelta only [biasE, div_one] using hx68
  let x70 : ℝ := Real.log (2 / 1)
  have hx70 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x70 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x71 : ℝ := (1 / 1)+(33493 / 125000)
  have hx71 : Bounds (158493 / 125000) (158493 / 125000) x71 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((33493 / 125000) : ℝ)) <;> norm_num
  let x72 : ℝ := (1 / 1)+(33493 / 125000)
  have hx72 : Bounds (158493 / 125000) (158493 / 125000) x72 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((33493 / 125000) : ℝ)) <;> norm_num
  let x73 : ℝ := Real.log x72
  have hx73 : Bounds (237396691 / 1000000000) (59349173 / 250000000) x73 := by
    exact bounds_log hx72 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x74 : ℝ := x71*x73
  have hx74 : Bounds (301005709973 / 1000000000000) (150502855621 / 500000000000) x74 := by
    apply bounds_mul hx71 hx73 <;> norm_num
  let x75 : ℝ := -(33493 / 125000)
  have hx75 : Bounds (-33493 / 125000) (-33493 / 125000) x75 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((33493 / 125000) : ℝ))
  let x76 : ℝ := (1 / 1)+x75
  have hx76 : Bounds (91507 / 125000) (91507 / 125000) x76 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx75 <;> norm_num
  let x77 : ℝ := (1 / 1)-(33493 / 125000)
  have hx77 : Bounds (91507 / 125000) (91507 / 125000) x77 := by
    exact hx76
  let x78 : ℝ := -(33493 / 125000)
  have hx78 : Bounds (-33493 / 125000) (-33493 / 125000) x78 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((33493 / 125000) : ℝ))
  let x79 : ℝ := (1 / 1)+x78
  have hx79 : Bounds (91507 / 125000) (91507 / 125000) x79 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx78 <;> norm_num
  let x80 : ℝ := (1 / 1)-(33493 / 125000)
  have hx80 : Bounds (91507 / 125000) (91507 / 125000) x80 := by
    exact hx79
  let x81 : ℝ := Real.log x80
  have hx81 : Bounds (-155949133 / 500000000) (-62379653 / 200000000) x81 := by
    exact bounds_log hx80 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x82 : ℝ := x77*x81
  have hx82 : Bounds (-45665399403 / 200000000000) (-114163498141 / 500000000000) x82 := by
    apply bounds_mul hx77 hx81 <;> norm_num
  let x83 : ℝ := x74+x82
  have hx83 : Bounds (36339356479 / 500000000000) (908483937 / 12500000000) x83 := by
    apply bounds_add hx74 hx82 <;> norm_num
  let x84 : ℝ := (2 / 1)⁻¹
  have hx84 : Bounds (1 / 2) (1 / 2) x84 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x85 : ℝ := x83*x84
  have hx85 : Bounds (36339356479 / 1000000000000) (908483937 / 25000000000) x85 := by
    apply bounds_mul hx83 hx84 <;> norm_num
  let x86 : ℝ := x83/(2 / 1)
  have hx86 : Bounds (36339356479 / 1000000000000) (908483937 / 25000000000) x86 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx85
  let x87 : ℝ := -x86
  have hx87 : Bounds (-908483937 / 25000000000) (-36339356479 / 1000000000000) x87 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx86
  let x88 : ℝ := x70+x87
  have hx88 : Bounds (16420195563 / 25000000000) (656807824521 / 1000000000000) x88 := by
    apply bounds_add hx70 hx87 <;> norm_num
  let x89 : ℝ := x70-x86
  have hx89 : Bounds (16420195563 / 25000000000) (656807824521 / 1000000000000) x89 := by
    exact hx88
  let x90 : ℝ := biasE (33493 / 125000)
  have hx90 : Bounds (16420195563 / 25000000000) (656807824521 / 1000000000000) x90 := by
    simpa +zetaDelta only [biasE, div_one] using hx89
  let y : ℝ := doubleCapHighTailY x
  have hEll' : Real.log 2 * doubleCapHighTailFloor x = x48 := by
    simpa +zetaDelta only [div_one] using hEll
  have hy : Bounds (836 / 3125) (33493 / 125000) y := by
    dsimp only [y, doubleCapHighTailY]
    apply entropyInverseBias_bracket hh0.le hh1.le
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (33493 / 125000) ≤ (656807824521 / 1000000000000) := hx90.2
      have h2 : (328404037537 / 500000000000) ≤ x48 := hx48.1
      linarith [hEll']
    · have h1 : x48 ≤ (328462003119 / 500000000000) := hx48.2
      have h2 : (328462088251 / 500000000000) ≤ biasE (836 / 3125) := hx69.1
      linarith [hEll']
  let x91 : ℝ := x⁻¹
  have hx91 : Bounds (2655601659751 / 500000000000) (5319480519481 / 1000000000000) x91 := by
    apply bounds_inv hx <;> norm_num
  let x92 : ℝ := x48*x91
  have hx92 : Bounds (54506894197 / 15625000000) (3494494453963 / 1000000000000) x92 := by
    apply bounds_mul hx48 hx91 <;> norm_num
  let x93 : ℝ := x48/x
  have hx93 : Bounds (54506894197 / 15625000000) (3494494453963 / 1000000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(192991 / 1000000)
  have hx95 : Bounds (1192991 / 1000000) (1192991 / 1000000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((192991 / 1000000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(192991 / 1000000)
  have hx96 : Bounds (1192991 / 1000000) (1192991 / 1000000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((192991 / 1000000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (176463599 / 1000000000) (441159 / 2500000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (105259742717 / 500000000000) (52629871657 / 250000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(192991 / 1000000)
  have hx99 : Bounds (-192991 / 1000000) (-192991 / 1000000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((192991 / 1000000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (807009 / 1000000) (807009 / 1000000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(192991 / 1000000)
  have hx101 : Bounds (807009 / 1000000) (807009 / 1000000) x101 := by
    exact hx100
  let x102 : ℝ := -(192991 / 1000000)
  have hx102 : Bounds (-192991 / 1000000) (-192991 / 1000000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((192991 / 1000000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (807009 / 1000000) (807009 / 1000000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(192991 / 1000000)
  have hx104 : Bounds (807009 / 1000000) (807009 / 1000000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-214420459 / 1000000000) (-107210229 / 500000000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-86519620099 / 500000000000) (-17303923939 / 100000000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (9370061309 / 250000000000) (18740123619 / 500000000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (9370061309 / 500000000000) (18740123619 / 1000000000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (9370061309 / 500000000000) (18740123619 / 1000000000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-18740123619 / 1000000000000) (-9370061309 / 500000000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (674407056381 / 1000000000000) (337203529191 / 500000000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (674407056381 / 1000000000000) (337203529191 / 500000000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (192991 / 1000000)
  have hx114 : Bounds (674407056381 / 1000000000000) (337203529191 / 500000000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(193309 / 1000000)
  have hx116 : Bounds (1193309 / 1000000) (1193309 / 1000000) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((193309 / 1000000) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(193309 / 1000000)
  have hx117 : Bounds (1193309 / 1000000) (1193309 / 1000000) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((193309 / 1000000) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (4418253 / 25000000) (176730121 / 1000000000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (210893642767 / 1000000000000) (210893643961 / 1000000000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(193309 / 1000000)
  have hx120 : Bounds (-193309 / 1000000) (-193309 / 1000000) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((193309 / 1000000) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (806691 / 1000000) (806691 / 1000000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(193309 / 1000000)
  have hx122 : Bounds (806691 / 1000000) (806691 / 1000000) x122 := by
    exact hx121
  let x123 : ℝ := -(193309 / 1000000)
  have hx123 : Bounds (-193309 / 1000000) (-193309 / 1000000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((193309 / 1000000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (806691 / 1000000) (806691 / 1000000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(193309 / 1000000)
  have hx125 : Bounds (806691 / 1000000) (806691 / 1000000) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-26851823 / 125000000) (-214814583 / 1000000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-86644495791 / 500000000000) (-86644495387 / 500000000000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (7520930237 / 200000000000) (37604653187 / 1000000000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (2350290699 / 125000000000) (9401163297 / 500000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (2350290699 / 125000000000) (9401163297 / 500000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-9401163297 / 500000000000) (-2350290699 / 125000000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (337172426703 / 500000000000) (42146553463 / 62500000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (337172426703 / 500000000000) (42146553463 / 62500000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (193309 / 1000000)
  have hx135 : Bounds (337172426703 / 500000000000) (42146553463 / 62500000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(192991 / 1000000)
  have hx136 : Bounds (13464755223 / 20000000000) (134881195833 / 200000000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((192991 / 1000000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(193309 / 1000000)
  have hx137 : Bounds (33717354273 / 50000000000) (337758614201 / 500000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((193309 / 1000000) : ℝ)) <;> norm_num
  let c : ℝ := doubleCapHighTailC x
  have hcMem := Reflection.regularContact_mem
    (x / (Real.log 2 * doubleCapHighTailFloor x))
  have hc0 : 0 ≤ c := by
    dsimp only [c, doubleCapHighTailC]
    apply GeneralCK.Certificates.RegularContactBounds.regularContact_nonneg
    exact div_nonneg hxPos0.le ((mul_pos log_two_pos hh0).le)
  have hcEq : biasE c = x93 * c := by
    have he := doubleCapHighTailC_equation x
    change c = (x / (Real.log 2 * doubleCapHighTailFloor x)) * biasE c at he
    rw [hEll'] at he
    have hxPos : 0 < x := hxPos0
    have hEllPos : 0 < x48 := by rw [← hEll']; exact mul_pos log_two_pos hh0
    change biasE c = (x48 / x) * c
    field_simp [hxPos.ne', hEllPos.ne'] at he ⊢
    nlinarith
  have hc : Bounds (192991 / 1000000) (193309 / 1000000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num)
      (by norm_num) (show 0 < x93 by linarith [hx93.1]) hcEq
    · have h1 : x93 * (192991 / 1000000) ≤ (134881195833 / 200000000000) := hx136.2
      have h2 : (674407056381 / 1000000000000) ≤ biasE (192991 / 1000000) := hx114.1
      linarith
    · have h1 : biasE (193309 / 1000000) ≤ (42146553463 / 62500000000) := hx135.2
      have h2 : (33717354273 / 50000000000) ≤ x93 * (193309 / 1000000) := hx137.1
      linarith
  let x138 : ℝ := (1 / 1)+x0
  have hx138 : Bounds (1409 / 1024) (881 / 640) x138 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx0 <;> norm_num
  let x139 : ℝ := -x0
  have hx139 : Bounds (-241 / 640) (-385 / 1024) x139 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x140 : ℝ := (1 / 1)+x139
  have hx140 : Bounds (399 / 640) (639 / 1024) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx139 <;> norm_num
  let x141 : ℝ := (1 / 1)-x0
  have hx141 : Bounds (399 / 640) (639 / 1024) x141 := by
    exact hx140
  let x142 : ℝ := x141⁻¹
  have hx142 : Bounds (1602503912363 / 1000000000000) (1604010025063 / 1000000000000) x142 := by
    apply bounds_inv hx141 <;> norm_num
  let x143 : ℝ := x138*x142
  have hx143 : Bounds (1102503912363 / 500000000000) (1104010025063 / 500000000000) x143 := by
    apply bounds_mul hx138 hx142 <;> norm_num
  let x144 : ℝ := x138/x141
  have hx144 : Bounds (1102503912363 / 500000000000) (1104010025063 / 500000000000) x144 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx143
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (49420691 / 62500000) (79209621 / 100000000) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_14.2)
  let x146 : ℝ := (2 / 1)⁻¹
  have hx146 : Bounds (1 / 2) (1 / 2) x146 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x147 : ℝ := x145*x146
  have hx147 : Bounds (49420691 / 125000000) (79209621 / 200000000) x147 := by
    apply bounds_mul hx145 hx146 <;> norm_num
  let x148 : ℝ := x145/(2 / 1)
  have hx148 : Bounds (49420691 / 125000000) (79209621 / 200000000) x148 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx147
  let x149 : ℝ := (1 / 1)+y
  have hx149 : Bounds (3961 / 3125) (158493 / 125000) x149 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x150 : ℝ := -y
  have hx150 : Bounds (-33493 / 125000) (-836 / 3125) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (91507 / 125000) (2289 / 3125) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-y
  have hx152 : Bounds (91507 / 125000) (2289 / 3125) x152 := by
    exact hx151
  let x153 : ℝ := x152⁻¹
  have hx153 : Bounds (682612494539 / 500000000000) (273203142929 / 200000000000) x153 := by
    apply bounds_inv hx152 <;> norm_num
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (432612494539 / 250000000000) (173203142929 / 100000000000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x149/x152
  have hx155 : Bounds (432612494539 / 250000000000) (173203142929 / 100000000000) x155 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx154
  let x156 : ℝ := Real.log x155
  have hx156 : Bounds (548381477 / 1000000000) (549294957 / 1000000000) x156 := by
    exact bounds_log hx155 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_16.2)
  let x157 : ℝ := (2 / 1)⁻¹
  have hx157 : Bounds (1 / 2) (1 / 2) x157 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x158 : ℝ := x156*x157
  have hx158 : Bounds (548381477 / 2000000000) (549294957 / 2000000000) x158 := by
    apply bounds_mul hx156 hx157 <;> norm_num
  let x159 : ℝ := x156/(2 / 1)
  have hx159 : Bounds (548381477 / 2000000000) (549294957 / 2000000000) x159 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx158
  let x160 : ℝ := (1 / 1)+c
  have hx160 : Bounds (1192991 / 1000000) (1193309 / 1000000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x161 : ℝ := -c
  have hx161 : Bounds (-193309 / 1000000) (-192991 / 1000000) x161 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x162 : ℝ := (1 / 1)+x161
  have hx162 : Bounds (806691 / 1000000) (807009 / 1000000) x162 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx161 <;> norm_num
  let x163 : ℝ := (1 / 1)-c
  have hx163 : Bounds (806691 / 1000000) (807009 / 1000000) x163 := by
    exact hx162
  let x164 : ℝ := x163⁻¹
  have hx164 : Bounds (1239143553541 / 1000000000000) (1239632027629 / 1000000000000) x164 := by
    apply bounds_inv hx163 <;> norm_num
  let x165 : ℝ := x160*x164
  have hx165 : Bounds (739143553541 / 500000000000) (739632027629 / 500000000000) x165 := by
    apply bounds_mul hx160 hx164 <;> norm_num
  let x166 : ℝ := x160/x163
  have hx166 : Bounds (739143553541 / 500000000000) (739632027629 / 500000000000) x166 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx165
  let x167 : ℝ := Real.log x166
  have hx167 : Bounds (390884057 / 1000000000) (78308941 / 200000000) x167 := by
    exact bounds_log hx166 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x168 : ℝ := (2 / 1)⁻¹
  have hx168 : Bounds (1 / 2) (1 / 2) x168 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x169 : ℝ := x167*x168
  have hx169 : Bounds (390884057 / 2000000000) (78308941 / 400000000) x169 := by
    apply bounds_mul hx167 hx168 <;> norm_num
  let x170 : ℝ := x167/(2 / 1)
  have hx170 : Bounds (390884057 / 2000000000) (78308941 / 400000000) x170 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx169
  let x171 : ℝ := Real.log (2 / 1)
  have hx171 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x171 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x172 : ℝ := c*c
  have hx172 : Bounds (37245526081 / 1000000000000) (37368369481 / 1000000000000) x172 := by
    apply bounds_mul hc hc <;> norm_num
  let x173 : ℝ := -x172
  have hx173 : Bounds (-37368369481 / 1000000000000) (-37245526081 / 1000000000000) x173 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx172
  let x174 : ℝ := (1 / 1)+x173
  have hx174 : Bounds (962631630519 / 1000000000000) (962754473919 / 1000000000000) x174 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx173 <;> norm_num
  let x175 : ℝ := (1 / 1)-x172
  have hx175 : Bounds (962631630519 / 1000000000000) (962754473919 / 1000000000000) x175 := by
    exact hx174
  let x176 : ℝ := Real.log x175
  have hx176 : Bounds (-2380279 / 62500000) (-37956859 / 1000000000) x176 := by
    exact bounds_log hx175 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (-2380279 / 125000000) (-37956859 / 2000000000) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (-2380279 / 125000000) (-37956859 / 2000000000) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (37956859 / 2000000000) (2380279 / 125000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x171+x180
  have hx181 : Bounds (1424251219 / 2000000000) (712189413 / 1000000000) x181 := by
    apply bounds_add hx171 hx180 <;> norm_num
  let x182 : ℝ := x171-x179
  have hx182 : Bounds (1424251219 / 2000000000) (712189413 / 1000000000) x182 := by
    exact hx181
  let x183 : ℝ := Real.log (2 / 1)
  have hx183 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x183 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x184 : ℝ := (1 / 1)+(193309 / 1000000)
  have hx184 : Bounds (1193309 / 1000000) (1193309 / 1000000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((193309 / 1000000) : ℝ)) <;> norm_num
  let x185 : ℝ := (1 / 1)+(193309 / 1000000)
  have hx185 : Bounds (1193309 / 1000000) (1193309 / 1000000) x185 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((193309 / 1000000) : ℝ)) <;> norm_num
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (4418253 / 25000000) (176730121 / 1000000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x187 : ℝ := x184*x186
  have hx187 : Bounds (210893642767 / 1000000000000) (210893643961 / 1000000000000) x187 := by
    apply bounds_mul hx184 hx186 <;> norm_num
  let x188 : ℝ := -(193309 / 1000000)
  have hx188 : Bounds (-193309 / 1000000) (-193309 / 1000000) x188 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((193309 / 1000000) : ℝ))
  let x189 : ℝ := (1 / 1)+x188
  have hx189 : Bounds (806691 / 1000000) (806691 / 1000000) x189 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx188 <;> norm_num
  let x190 : ℝ := (1 / 1)-(193309 / 1000000)
  have hx190 : Bounds (806691 / 1000000) (806691 / 1000000) x190 := by
    exact hx189
  let x191 : ℝ := -(193309 / 1000000)
  have hx191 : Bounds (-193309 / 1000000) (-193309 / 1000000) x191 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((193309 / 1000000) : ℝ))
  let x192 : ℝ := (1 / 1)+x191
  have hx192 : Bounds (806691 / 1000000) (806691 / 1000000) x192 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx191 <;> norm_num
  let x193 : ℝ := (1 / 1)-(193309 / 1000000)
  have hx193 : Bounds (806691 / 1000000) (806691 / 1000000) x193 := by
    exact hx192
  let x194 : ℝ := Real.log x193
  have hx194 : Bounds (-26851823 / 125000000) (-214814583 / 1000000000) x194 := by
    exact bounds_log hx193 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x195 : ℝ := x190*x194
  have hx195 : Bounds (-86644495791 / 500000000000) (-86644495387 / 500000000000) x195 := by
    apply bounds_mul hx190 hx194 <;> norm_num
  let x196 : ℝ := x187+x195
  have hx196 : Bounds (7520930237 / 200000000000) (37604653187 / 1000000000000) x196 := by
    apply bounds_add hx187 hx195 <;> norm_num
  let x197 : ℝ := (2 / 1)⁻¹
  have hx197 : Bounds (1 / 2) (1 / 2) x197 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x198 : ℝ := x196*x197
  have hx198 : Bounds (2350290699 / 125000000000) (9401163297 / 500000000000) x198 := by
    apply bounds_mul hx196 hx197 <;> norm_num
  let x199 : ℝ := x196/(2 / 1)
  have hx199 : Bounds (2350290699 / 125000000000) (9401163297 / 500000000000) x199 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx198
  let x200 : ℝ := -x199
  have hx200 : Bounds (-9401163297 / 500000000000) (-2350290699 / 125000000000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx199
  let x201 : ℝ := x183+x200
  have hx201 : Bounds (337172426703 / 500000000000) (42146553463 / 62500000000) x201 := by
    apply bounds_add hx183 hx200 <;> norm_num
  let x202 : ℝ := x183-x199
  have hx202 : Bounds (337172426703 / 500000000000) (42146553463 / 62500000000) x202 := by
    exact hx201
  let x203 : ℝ := biasE (193309 / 1000000)
  have hx203 : Bounds (337172426703 / 500000000000) (42146553463 / 62500000000) x203 := by
    simpa +zetaDelta only [biasE, div_one] using hx202
  let x204 : ℝ := Real.log (2 / 1)
  have hx204 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x204 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x205 : ℝ := (1 / 1)+(192991 / 1000000)
  have hx205 : Bounds (1192991 / 1000000) (1192991 / 1000000) x205 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((192991 / 1000000) : ℝ)) <;> norm_num
  let x206 : ℝ := (1 / 1)+(192991 / 1000000)
  have hx206 : Bounds (1192991 / 1000000) (1192991 / 1000000) x206 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((192991 / 1000000) : ℝ)) <;> norm_num
  let x207 : ℝ := Real.log x206
  have hx207 : Bounds (176463599 / 1000000000) (441159 / 2500000) x207 := by
    exact bounds_log hx206 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x208 : ℝ := x205*x207
  have hx208 : Bounds (105259742717 / 500000000000) (52629871657 / 250000000000) x208 := by
    apply bounds_mul hx205 hx207 <;> norm_num
  let x209 : ℝ := -(192991 / 1000000)
  have hx209 : Bounds (-192991 / 1000000) (-192991 / 1000000) x209 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((192991 / 1000000) : ℝ))
  let x210 : ℝ := (1 / 1)+x209
  have hx210 : Bounds (807009 / 1000000) (807009 / 1000000) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx209 <;> norm_num
  let x211 : ℝ := (1 / 1)-(192991 / 1000000)
  have hx211 : Bounds (807009 / 1000000) (807009 / 1000000) x211 := by
    exact hx210
  let x212 : ℝ := -(192991 / 1000000)
  have hx212 : Bounds (-192991 / 1000000) (-192991 / 1000000) x212 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((192991 / 1000000) : ℝ))
  let x213 : ℝ := (1 / 1)+x212
  have hx213 : Bounds (807009 / 1000000) (807009 / 1000000) x213 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx212 <;> norm_num
  let x214 : ℝ := (1 / 1)-(192991 / 1000000)
  have hx214 : Bounds (807009 / 1000000) (807009 / 1000000) x214 := by
    exact hx213
  let x215 : ℝ := Real.log x214
  have hx215 : Bounds (-214420459 / 1000000000) (-107210229 / 500000000) x215 := by
    exact bounds_log hx214 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x216 : ℝ := x211*x215
  have hx216 : Bounds (-86519620099 / 500000000000) (-17303923939 / 100000000000) x216 := by
    apply bounds_mul hx211 hx215 <;> norm_num
  let x217 : ℝ := x208+x216
  have hx217 : Bounds (9370061309 / 250000000000) (18740123619 / 500000000000) x217 := by
    apply bounds_add hx208 hx216 <;> norm_num
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (9370061309 / 500000000000) (18740123619 / 1000000000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (9370061309 / 500000000000) (18740123619 / 1000000000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := -x220
  have hx221 : Bounds (-18740123619 / 1000000000000) (-9370061309 / 500000000000) x221 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx220
  let x222 : ℝ := x204+x221
  have hx222 : Bounds (674407056381 / 1000000000000) (337203529191 / 500000000000) x222 := by
    apply bounds_add hx204 hx221 <;> norm_num
  let x223 : ℝ := x204-x220
  have hx223 : Bounds (674407056381 / 1000000000000) (337203529191 / 500000000000) x223 := by
    exact hx222
  let x224 : ℝ := biasE (192991 / 1000000)
  have hx224 : Bounds (674407056381 / 1000000000000) (337203529191 / 500000000000) x224 := by
    simpa +zetaDelta only [biasE, div_one] using hx223
  let x225 : ℝ := biasE c
  have hx225 : Bounds (337172426703 / 500000000000) (337203529191 / 500000000000) x225 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx203.1 hx224.2
  let x226 : ℝ := x159⁻¹
  have hx226 : Bounds (91025776521 / 25000000000) (455887024791 / 125000000000) x226 := by
    apply bounds_inv hx159 <;> norm_num
  let x227 : ℝ := x148*x226
  have hx227 : Bounds (1439538167833 / 1000000000000) (1444425538101 / 1000000000000) x227 := by
    apply bounds_mul hx148 hx226 <;> norm_num
  let x228 : ℝ := x148/x159
  have hx228 : Bounds (1439538167833 / 1000000000000) (1444425538101 / 1000000000000) x228 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx227
  let x229 : ℝ := c*x148
  have hx229 : Bounds (38150994307 / 500000000000) (7655966313 / 100000000000) x229 := by
    apply bounds_mul hc hx148 <;> norm_num
  let x230 : ℝ := x225+x229
  have hx230 : Bounds (37532342101 / 50000000000) (93870840189 / 125000000000) x230 := by
    apply bounds_add hx225 hx229 <;> norm_num
  let x231 : ℝ := x*x170
  have hx231 : Bounds (36740811021 / 1000000000000) (7372052649 / 200000000000) x231 := by
    apply bounds_mul hx hx170 <;> norm_num
  let x232 : ℝ := x48+x231
  have hx232 : Bounds (138709777219 / 200000000000) (693784269483 / 1000000000000) x232 := by
    apply bounds_add hx48 hx231 <;> norm_num
  let x233 : ℝ := x232⁻¹
  have hx233 : Bounds (720685120711 / 500000000000) (1441859427719 / 1000000000000) x233 := by
    apply bounds_inv hx232 <;> norm_num
  let x234 : ℝ := x230*x233
  have hx234 : Bounds (216392003981 / 200000000000) (270697111829 / 250000000000) x234 := by
    apply bounds_mul hx230 hx233 <;> norm_num
  let x235 : ℝ := x230/x232
  have hx235 : Bounds (216392003981 / 200000000000) (270697111829 / 250000000000) x235 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx234
  let x236 : ℝ := y*y
  have hx236 : Bounds (698896 / 9765625) (1121781049 / 15625000000) x236 := by
    apply bounds_mul hy hy <;> norm_num
  let x237 : ℝ := -x236
  have hx237 : Bounds (-1121781049 / 15625000000) (-698896 / 9765625) x237 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx236
  let x238 : ℝ := (1 / 1)+x237
  have hx238 : Bounds (14503218951 / 15625000000) (9066729 / 9765625) x238 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx237 <;> norm_num
  let x239 : ℝ := (1 / 1)-x236
  have hx239 : Bounds (14503218951 / 15625000000) (9066729 / 9765625) x239 := by
    exact hx238
  let x240 : ℝ := x239*x159
  have hx240 : Bounds (254505492147 / 1000000000000) (254991796029 / 1000000000000) x240 := by
    apply bounds_mul hx239 hx159 <;> norm_num
  let x241 : ℝ := c*c
  have hx241 : Bounds (37245526081 / 1000000000000) (37368369481 / 1000000000000) x241 := by
    apply bounds_mul hc hc <;> norm_num
  let x242 : ℝ := -x241
  have hx242 : Bounds (-37368369481 / 1000000000000) (-37245526081 / 1000000000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx241
  let x243 : ℝ := (1 / 1)+x242
  have hx243 : Bounds (962631630519 / 1000000000000) (962754473919 / 1000000000000) x243 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx242 <;> norm_num
  let x244 : ℝ := (1 / 1)-x241
  have hx244 : Bounds (962631630519 / 1000000000000) (962754473919 / 1000000000000) x244 := by
    exact hx243
  let x245 : ℝ := x244*x182
  have hx245 : Bounds (685514636607 / 1000000000000) (171415885911 / 250000000000) x245 := by
    apply bounds_mul hx244 hx182 <;> norm_num
  let x246 : ℝ := y*y
  have hx246 : Bounds (698896 / 9765625) (1121781049 / 15625000000) x246 := by
    apply bounds_mul hy hy <;> norm_num
  let x247 : ℝ := (1 / 1)+x246
  have hx247 : Bounds (10464521 / 9765625) (16746781049 / 15625000000) x247 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx246 <;> norm_num
  let x248 : ℝ := x247*x159
  have hx248 : Bounds (146906866741 / 500000000000) (294365516039 / 1000000000000) x248 := by
    apply bounds_mul hx247 hx159 <;> norm_num
  let x249 : ℝ := -y
  have hx249 : Bounds (-33493 / 125000) (-836 / 3125) x249 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x250 : ℝ := x248+x249
  have hx250 : Bounds (12934866741 / 500000000000) (26845516039 / 1000000000000) x250 := by
    apply bounds_add hx248 hx249 <;> norm_num
  let x251 : ℝ := x248-y
  have hx251 : Bounds (12934866741 / 500000000000) (26845516039 / 1000000000000) x251 := by
    exact hx250
  let x252 : ℝ := x240*x240
  have hx252 : Bounds (16193261383 / 250000000000) (65020816043 / 1000000000000) x252 := by
    apply bounds_mul hx240 hx240 <;> norm_num
  let x253 : ℝ := x252⁻¹
  have hx253 : Bounds (15379690087843 / 1000000000000) (771926031721 / 50000000000) x253 := by
    apply bounds_inv hx252 <;> norm_num
  let x254 : ℝ := x251*x253
  have hx254 : Bounds (49733560451 / 125000000000) (41445505331 / 100000000000) x254 := by
    apply bounds_mul hx251 hx253 <;> norm_num
  let x255 : ℝ := x251/x252
  have hx255 : Bounds (49733560451 / 125000000000) (41445505331 / 100000000000) x255 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx254
  let x256 : ℝ := (-2 / 1)*x255
  have hx256 : Bounds (-41445505331 / 50000000000) (-49733560451 / 62500000000) x256 := by
    apply bounds_mul (bounds_const ((-2 / 1) : ℝ)) hx255 <;> norm_num
  let x257 : ℝ := x256*x228
  have hx257 : Bounds (-149662365849 / 125000000000) (-1145493735863 / 1000000000000) x257 := by
    apply bounds_mul hx256 hx228 <;> norm_num
  let x258 : ℝ := (2 / 1)*x182
  have hx258 : Bounds (1424251219 / 1000000000) (712189413 / 500000000) x258 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx182 <;> norm_num
  let x259 : ℝ := c*c
  have hx259 : Bounds (37245526081 / 1000000000000) (37368369481 / 1000000000000) x259 := by
    apply bounds_mul hc hc <;> norm_num
  let x260 : ℝ := -x259
  have hx260 : Bounds (-37368369481 / 1000000000000) (-37245526081 / 1000000000000) x260 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx259
  let x261 : ℝ := x258+x260
  have hx261 : Bounds (1386882849519 / 1000000000000) (1387133299919 / 1000000000000) x261 := by
    apply bounds_add hx258 hx260 <;> norm_num
  let x262 : ℝ := x258-x259
  have hx262 : Bounds (1386882849519 / 1000000000000) (1387133299919 / 1000000000000) x262 := by
    exact hx261
  let x263 : ℝ := c*x262
  have hx263 : Bounds (267655908011 / 1000000000000) (10725814043 / 40000000000) x263 := by
    apply bounds_mul hc hx262 <;> norm_num
  let x264 : ℝ := x245*x245
  have hx264 : Bounds (234965158501 / 500000000000) (470134495083 / 1000000000000) x264 := by
    apply bounds_mul hx245 hx245 <;> norm_num
  let x265 : ℝ := x264⁻¹
  have hx265 : Bounds (33235170283 / 15625000000) (1063987535833 / 500000000000) x265 := by
    apply bounds_inv hx264 <;> norm_num
  let x266 : ℝ := x263*x265
  have hx266 : Bounds (569317739519 / 1000000000000) (570606622671 / 1000000000000) x266 := by
    apply bounds_mul hx263 hx265 <;> norm_num
  let x267 : ℝ := x263/x264
  have hx267 : Bounds (569317739519 / 1000000000000) (570606622671 / 1000000000000) x267 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx266
  let x268 : ℝ := (2 / 1)*x267
  have hx268 : Bounds (569317739519 / 500000000000) (570606622671 / 500000000000) x268 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx267 <;> norm_num
  let x269 : ℝ := x268*x235
  have hx269 : Bounds (307989516391 / 250000000000) (1235692517981 / 1000000000000) x269 := by
    apply bounds_mul hx268 hx235 <;> norm_num
  let x270 : ℝ := x257+x269
  have hx270 : Bounds (8664784693 / 250000000000) (45099391059 / 500000000000) x270 := by
    apply bounds_add hx257 hx269 <;> norm_num
  have hPos : 0 < x270 :=
    lt_of_lt_of_le (by norm_num) hx270.1
  have hBridgeL : doubleCapBridgeL x = x48 := by
    exact hEll'
  rw [← doubleCapBridgeDerivativeTraceForm_eq x]
  simpa +zetaDelta only [doubleCapBridgeDerivativeTraceForm,
    hBridgeL, SmallMean.A, biasB, div_one, pow_two] using hPos

theorem acceptedCell : DoubleCapBridgeDerivativeCellCertificate
    (⟨215, by decide⟩ : Fin 256) doubleCapBridgeDerivativeExpression where
  positive x hx := by
    have hloEq : doubleCapBridgeLo (⟨215, by decide⟩ : Fin 256) =
        (385 / 2048) := by norm_num [doubleCapBridgeLo, doubleCapBridgeStep]
    have hhiEq : doubleCapBridgeHi (⟨215, by decide⟩ : Fin 256) =
        (241 / 1280) := by norm_num [doubleCapBridgeHi, doubleCapBridgeStep]
    have hlo : (385 / 2048) ≤ x := by
      simpa only [hloEq] using hx.1
    have hhi : x ≤ (241 / 1280) := by
      simpa only [hhiEq] using hx.2
    exact cell_derivative_pos x ⟨hlo, hhi⟩

#print axioms cell_derivative_pos
#print axioms acceptedCell

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell215

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell216 =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell216
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_derivative_pos (x : ℝ)
    (hx : Bounds (241 / 1280) (1931 / 10240) x) :
    0 < doubleCapBridgeDerivativeExpression x := by
  have hxPos0 : 0 < x := by linarith [hx.1]
  have hxHalf : x < 1 / 2 := by linarith [hx.2]
  have hh0 : 0 < doubleCapHighTailFloor x :=
    doubleCapHighTailFloor_pos hxPos0 hxHalf
  have hh1 : doubleCapHighTailFloor x < 1 := by
    have hfloor := doubleCapHighFloor_lt_entropyCap
      (m := (1 - x) / 2) (by linarith) (by linarith)
    have hH1 := H_le_one ((1 - x) / 2)
    unfold doubleCapHighTailFloor
    have heq : 2 * ((1 - x) / 2) - 1 / 2 =
        (1 - 2 * x) / 2 := by ring
    rw [heq] at hfloor
    linarith
  have hEq : biasE (2 * x) = Real.log 2 * H ((1 - 2 * x) / 2) := by
    rw [show 2 * x = 1 - 2 * ((1 - 2 * x) / 2) by ring,
      GeneralCK.Correction.Natural.biasE_probability (by linarith)
        (by linarith), GeneralCK.Certificates.Mixed.hn_eq_H_mul_log]
    ring
  have hEll : Real.log 2 * doubleCapHighTailFloor x =
      (Real.log 2 + biasE (2 * x)) / 2 := by
    dsimp [doubleCapHighTailFloor]
    rw [hEq]
    ring
  let x0 : ℝ := (2 / 1)*x
  have hx0 : Bounds (241 / 640) (1931 / 5120) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx <;> norm_num
  let x1 : ℝ := Real.log (2 / 1)
  have hx1 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x1 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x2 : ℝ := Real.log (2 / 1)
  have hx2 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x2 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x3 : ℝ := (1 / 1)+(1931 / 5120)
  have hx3 : Bounds (7051 / 5120) (7051 / 5120) x3 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1931 / 5120) : ℝ)) <;> norm_num
  let x4 : ℝ := (1 / 1)+(1931 / 5120)
  have hx4 : Bounds (7051 / 5120) (7051 / 5120) x4 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1931 / 5120) : ℝ)) <;> norm_num
  let x5 : ℝ := Real.log x4
  have hx5 : Bounds (320015011 / 1000000000) (80003753 / 250000000) x5 := by
    exact bounds_log hx4 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x6 : ℝ := x3*x5
  have hx6 : Bounds (3525665379 / 8000000000) (440708173753 / 1000000000000) x6 := by
    apply bounds_mul hx3 hx5 <;> norm_num
  let x7 : ℝ := -(1931 / 5120)
  have hx7 : Bounds (-1931 / 5120) (-1931 / 5120) x7 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1931 / 5120) : ℝ))
  let x8 : ℝ := (1 / 1)+x7
  have hx8 : Bounds (3189 / 5120) (3189 / 5120) x8 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx7 <;> norm_num
  let x9 : ℝ := (1 / 1)-(1931 / 5120)
  have hx9 : Bounds (3189 / 5120) (3189 / 5120) x9 := by
    exact hx8
  let x10 : ℝ := -(1931 / 5120)
  have hx10 : Bounds (-1931 / 5120) (-1931 / 5120) x10 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1931 / 5120) : ℝ))
  let x11 : ℝ := (1 / 1)+x10
  have hx11 : Bounds (3189 / 5120) (3189 / 5120) x11 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx10 <;> norm_num
  let x12 : ℝ := (1 / 1)-(1931 / 5120)
  have hx12 : Bounds (3189 / 5120) (3189 / 5120) x12 := by
    exact hx11
  let x13 : ℝ := Real.log x12
  have hx13 : Bounds (-118361763 / 250000000) (-473447051 / 1000000000) x13 := by
    exact bounds_log hx12 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x14 : ℝ := x9*x13
  have hx14 : Bounds (-2948872361 / 10000000000) (-73721808869 / 250000000000) x14 := by
    apply bounds_mul hx9 hx13 <;> norm_num
  let x15 : ℝ := x6+x14
  have hx15 : Bounds (5832837451 / 40000000000) (145820938277 / 1000000000000) x15 := by
    apply bounds_add hx6 hx14 <;> norm_num
  let x16 : ℝ := (2 / 1)⁻¹
  have hx16 : Bounds (1 / 2) (1 / 2) x16 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x17 : ℝ := x15*x16
  have hx17 : Bounds (72910468137 / 1000000000000) (72910469139 / 1000000000000) x17 := by
    apply bounds_mul hx15 hx16 <;> norm_num
  let x18 : ℝ := x15/(2 / 1)
  have hx18 : Bounds (72910468137 / 1000000000000) (72910469139 / 1000000000000) x18 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx17
  let x19 : ℝ := -x18
  have hx19 : Bounds (-72910469139 / 1000000000000) (-72910468137 / 1000000000000) x19 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx18
  let x20 : ℝ := x2+x19
  have hx20 : Bounds (620236710861 / 1000000000000) (620236712863 / 1000000000000) x20 := by
    apply bounds_add hx2 hx19 <;> norm_num
  let x21 : ℝ := x2-x18
  have hx21 : Bounds (620236710861 / 1000000000000) (620236712863 / 1000000000000) x21 := by
    exact hx20
  let x22 : ℝ := biasE (1931 / 5120)
  have hx22 : Bounds (620236710861 / 1000000000000) (620236712863 / 1000000000000) x22 := by
    simpa +zetaDelta only [biasE, div_one] using hx21
  let x23 : ℝ := Real.log (2 / 1)
  have hx23 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x23 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x24 : ℝ := (1 / 1)+(241 / 640)
  have hx24 : Bounds (881 / 640) (881 / 640) x24 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((241 / 640) : ℝ)) <;> norm_num
  let x25 : ℝ := (1 / 1)+(241 / 640)
  have hx25 : Bounds (881 / 640) (881 / 640) x25 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((241 / 640) : ℝ)) <;> norm_num
  let x26 : ℝ := Real.log x25
  have hx26 : Bounds (319589449 / 1000000000) (6391789 / 20000000) x26 := by
    exact bounds_log hx25 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x27 : ℝ := x24*x26
  have hx27 : Bounds (439934850889 / 1000000000000) (219967426133 / 500000000000) x27 := by
    apply bounds_mul hx24 hx26 <;> norm_num
  let x28 : ℝ := -(241 / 640)
  have hx28 : Bounds (-241 / 640) (-241 / 640) x28 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((241 / 640) : ℝ))
  let x29 : ℝ := (1 / 1)+x28
  have hx29 : Bounds (399 / 640) (399 / 640) x29 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx28 <;> norm_num
  let x30 : ℝ := (1 / 1)-(241 / 640)
  have hx30 : Bounds (399 / 640) (399 / 640) x30 := by
    exact hx29
  let x31 : ℝ := -(241 / 640)
  have hx31 : Bounds (-241 / 640) (-241 / 640) x31 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((241 / 640) : ℝ))
  let x32 : ℝ := (1 / 1)+x31
  have hx32 : Bounds (399 / 640) (399 / 640) x32 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx31 <;> norm_num
  let x33 : ℝ := (1 / 1)-(241 / 640)
  have hx33 : Bounds (399 / 640) (399 / 640) x33 := by
    exact hx32
  let x34 : ℝ := Real.log x33
  have hx34 : Bounds (-11812669 / 25000000) (-472506759 / 1000000000) x34 := by
    exact bounds_log hx33 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x35 : ℝ := x30*x34
  have hx35 : Bounds (-73644608297 / 250000000000) (-73644608141 / 250000000000) x35 := by
    apply bounds_mul hx30 hx34 <;> norm_num
  let x36 : ℝ := x27+x35
  have hx36 : Bounds (145356417701 / 1000000000000) (72678209851 / 500000000000) x36 := by
    apply bounds_add hx27 hx35 <;> norm_num
  let x37 : ℝ := (2 / 1)⁻¹
  have hx37 : Bounds (1 / 2) (1 / 2) x37 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x38 : ℝ := x36*x37
  have hx38 : Bounds (1453564177 / 20000000000) (72678209851 / 1000000000000) x38 := by
    apply bounds_mul hx36 hx37 <;> norm_num
  let x39 : ℝ := x36/(2 / 1)
  have hx39 : Bounds (1453564177 / 20000000000) (72678209851 / 1000000000000) x39 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx38
  let x40 : ℝ := -x39
  have hx40 : Bounds (-72678209851 / 1000000000000) (-1453564177 / 20000000000) x40 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx39
  let x41 : ℝ := x23+x40
  have hx41 : Bounds (620468970149 / 1000000000000) (12409379443 / 20000000000) x41 := by
    apply bounds_add hx23 hx40 <;> norm_num
  let x42 : ℝ := x23-x39
  have hx42 : Bounds (620468970149 / 1000000000000) (12409379443 / 20000000000) x42 := by
    exact hx41
  let x43 : ℝ := biasE (241 / 640)
  have hx43 : Bounds (620468970149 / 1000000000000) (12409379443 / 20000000000) x43 := by
    simpa +zetaDelta only [biasE, div_one] using hx42
  let x44 : ℝ := biasE x0
  have hx44 : Bounds (620236710861 / 1000000000000) (12409379443 / 20000000000) x44 := by
    exact bounds_biasE hx0 (by norm_num) (by norm_num) hx22.1 hx43.2
  let x45 : ℝ := x1+x44
  have hx45 : Bounds (1313383890861 / 1000000000000) (26272323063 / 20000000000) x45 := by
    apply bounds_add hx1 hx44 <;> norm_num
  let x46 : ℝ := (2 / 1)⁻¹
  have hx46 : Bounds (1 / 2) (1 / 2) x46 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x47 : ℝ := x45*x46
  have hx47 : Bounds (65669194543 / 100000000000) (26272323063 / 40000000000) x47 := by
    apply bounds_mul hx45 hx46 <;> norm_num
  let x48 : ℝ := x45/(2 / 1)
  have hx48 : Bounds (65669194543 / 100000000000) (26272323063 / 40000000000) x48 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx47
  let x49 : ℝ := Real.log (2 / 1)
  have hx49 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x49 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x50 : ℝ := (1 / 1)+(267943 / 1000000)
  have hx50 : Bounds (1267943 / 1000000) (1267943 / 1000000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((267943 / 1000000) : ℝ)) <;> norm_num
  let x51 : ℝ := (1 / 1)+(267943 / 1000000)
  have hx51 : Bounds (1267943 / 1000000) (1267943 / 1000000) x51 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((267943 / 1000000) : ℝ)) <;> norm_num
  let x52 : ℝ := Real.log x51
  have hx52 : Bounds (118697951 / 500000000) (237395903 / 1000000000) x52 := by
    exact bounds_log hx51 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x53 : ℝ := x50*x52
  have hx53 : Bounds (301004472169 / 1000000000000) (150502236719 / 500000000000) x53 := by
    apply bounds_mul hx50 hx52 <;> norm_num
  let x54 : ℝ := -(267943 / 1000000)
  have hx54 : Bounds (-267943 / 1000000) (-267943 / 1000000) x54 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((267943 / 1000000) : ℝ))
  let x55 : ℝ := (1 / 1)+x54
  have hx55 : Bounds (732057 / 1000000) (732057 / 1000000) x55 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx54 <;> norm_num
  let x56 : ℝ := (1 / 1)-(267943 / 1000000)
  have hx56 : Bounds (732057 / 1000000) (732057 / 1000000) x56 := by
    exact hx55
  let x57 : ℝ := -(267943 / 1000000)
  have hx57 : Bounds (-267943 / 1000000) (-267943 / 1000000) x57 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((267943 / 1000000) : ℝ))
  let x58 : ℝ := (1 / 1)+x57
  have hx58 : Bounds (732057 / 1000000) (732057 / 1000000) x58 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx57 <;> norm_num
  let x59 : ℝ := (1 / 1)-(267943 / 1000000)
  have hx59 : Bounds (732057 / 1000000) (732057 / 1000000) x59 := by
    exact hx58
  let x60 : ℝ := Real.log x59
  have hx60 : Bounds (-3118969 / 10000000) (-311896899 / 1000000000) x60 := by
    exact bounds_log hx59 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x61 : ℝ := x56*x60
  have hx61 : Bounds (-57081577231 / 250000000000) (-228326308191 / 1000000000000) x61 := by
    apply bounds_mul hx56 hx60 <;> norm_num
  let x62 : ℝ := x53+x61
  have hx62 : Bounds (14535632649 / 200000000000) (72678165247 / 1000000000000) x62 := by
    apply bounds_add hx53 hx61 <;> norm_num
  let x63 : ℝ := (2 / 1)⁻¹
  have hx63 : Bounds (1 / 2) (1 / 2) x63 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x64 : ℝ := x62*x63
  have hx64 : Bounds (18169540811 / 500000000000) (283899083 / 7812500000) x64 := by
    apply bounds_mul hx62 hx63 <;> norm_num
  let x65 : ℝ := x62/(2 / 1)
  have hx65 : Bounds (18169540811 / 500000000000) (283899083 / 7812500000) x65 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx64
  let x66 : ℝ := -x65
  have hx66 : Bounds (-283899083 / 7812500000) (-18169540811 / 500000000000) x66 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx65
  let x67 : ℝ := x49+x66
  have hx67 : Bounds (20525253043 / 31250000000) (328404049689 / 500000000000) x67 := by
    apply bounds_add hx49 hx66 <;> norm_num
  let x68 : ℝ := x49-x65
  have hx68 : Bounds (20525253043 / 31250000000) (328404049689 / 500000000000) x68 := by
    exact hx67
  let x69 : ℝ := biasE (267943 / 1000000)
  have hx69 : Bounds (20525253043 / 31250000000) (328404049689 / 500000000000) x69 := by
    simpa +zetaDelta only [biasE, div_one] using hx68
  let x70 : ℝ := Real.log (2 / 1)
  have hx70 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x70 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x71 : ℝ := (1 / 1)+(134183 / 500000)
  have hx71 : Bounds (634183 / 500000) (634183 / 500000) x71 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((134183 / 500000) : ℝ)) <;> norm_num
  let x72 : ℝ := (1 / 1)+(134183 / 500000)
  have hx72 : Bounds (634183 / 500000) (634183 / 500000) x72 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((134183 / 500000) : ℝ)) <;> norm_num
  let x73 : ℝ := Real.log x72
  have hx73 : Bounds (237729457 / 1000000000) (118864729 / 500000000) x73 := by
    exact bounds_log hx72 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x74 : ℝ := x71*x73
  have hx74 : Bounds (301527960457 / 1000000000000) (150763980863 / 500000000000) x74 := by
    apply bounds_mul hx71 hx73 <;> norm_num
  let x75 : ℝ := -(134183 / 500000)
  have hx75 : Bounds (-134183 / 500000) (-134183 / 500000) x75 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((134183 / 500000) : ℝ))
  let x76 : ℝ := (1 / 1)+x75
  have hx76 : Bounds (365817 / 500000) (365817 / 500000) x76 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx75 <;> norm_num
  let x77 : ℝ := (1 / 1)-(134183 / 500000)
  have hx77 : Bounds (365817 / 500000) (365817 / 500000) x77 := by
    exact hx76
  let x78 : ℝ := -(134183 / 500000)
  have hx78 : Bounds (-134183 / 500000) (-134183 / 500000) x78 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((134183 / 500000) : ℝ))
  let x79 : ℝ := (1 / 1)+x78
  have hx79 : Bounds (365817 / 500000) (365817 / 500000) x79 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx78 <;> norm_num
  let x80 : ℝ := (1 / 1)-(134183 / 500000)
  have hx80 : Bounds (365817 / 500000) (365817 / 500000) x80 := by
    exact hx79
  let x81 : ℝ := Real.log x80
  have hx81 : Bounds (-312474891 / 1000000000) (-31247489 / 100000000) x81 := by
    exact bounds_log hx80 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x82 : ℝ := x77*x81
  have hx82 : Bounds (-114308627201 / 500000000000) (-22861725367 / 100000000000) x82 := by
    apply bounds_mul hx77 hx81 <;> norm_num
  let x83 : ℝ := x74+x82
  have hx83 : Bounds (14582141211 / 200000000000) (9113838507 / 125000000000) x83 := by
    apply bounds_add hx74 hx82 <;> norm_num
  let x84 : ℝ := (2 / 1)⁻¹
  have hx84 : Bounds (1 / 2) (1 / 2) x84 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x85 : ℝ := x83*x84
  have hx85 : Bounds (36455353027 / 1000000000000) (9113838507 / 250000000000) x85 := by
    apply bounds_mul hx83 hx84 <;> norm_num
  let x86 : ℝ := x83/(2 / 1)
  have hx86 : Bounds (36455353027 / 1000000000000) (9113838507 / 250000000000) x86 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx85
  let x87 : ℝ := -x86
  have hx87 : Bounds (-9113838507 / 250000000000) (-36455353027 / 1000000000000) x87 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx86
  let x88 : ℝ := x70+x87
  have hx88 : Bounds (164172956493 / 250000000000) (656691827973 / 1000000000000) x88 := by
    apply bounds_add hx70 hx87 <;> norm_num
  let x89 : ℝ := x70-x86
  have hx89 : Bounds (164172956493 / 250000000000) (656691827973 / 1000000000000) x89 := by
    exact hx88
  let x90 : ℝ := biasE (134183 / 500000)
  have hx90 : Bounds (164172956493 / 250000000000) (656691827973 / 1000000000000) x90 := by
    simpa +zetaDelta only [biasE, div_one] using hx89
  let y : ℝ := doubleCapHighTailY x
  have hEll' : Real.log 2 * doubleCapHighTailFloor x = x48 := by
    simpa +zetaDelta only [div_one] using hEll
  have hy : Bounds (267943 / 1000000) (134183 / 500000) y := by
    dsimp only [y, doubleCapHighTailY]
    apply entropyInverseBias_bracket hh0.le hh1.le
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (134183 / 500000) ≤ (656691827973 / 1000000000000) := hx90.2
      have h2 : (65669194543 / 100000000000) ≤ x48 := hx48.1
      linarith [hEll']
    · have h1 : x48 ≤ (26272323063 / 40000000000) := hx48.2
      have h2 : (20525253043 / 31250000000) ≤ biasE (267943 / 1000000) := hx69.1
      linarith [hEll']
  let x91 : ℝ := x⁻¹
  have hx91 : Bounds (212118073537 / 40000000000) (5311203319503 / 1000000000000) x91 := by
    apply bounds_inv hx <;> norm_num
  let x92 : ℝ := x48*x91
  have hx92 : Bounds (54412589989 / 15625000000) (1744220618291 / 500000000000) x92 := by
    apply bounds_mul hx48 hx91 <;> norm_num
  let x93 : ℝ := x48/x
  have hx93 : Bounds (54412589989 / 15625000000) (1744220618291 / 500000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(48327 / 250000)
  have hx95 : Bounds (298327 / 250000) (298327 / 250000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((48327 / 250000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(48327 / 250000)
  have hx96 : Bounds (298327 / 250000) (298327 / 250000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((48327 / 250000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (88364641 / 500000000) (176729283 / 1000000000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (52723116511 / 250000000000) (210892467239 / 1000000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(48327 / 250000)
  have hx99 : Bounds (-48327 / 250000) (-48327 / 250000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((48327 / 250000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (201673 / 250000) (201673 / 250000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(48327 / 250000)
  have hx101 : Bounds (201673 / 250000) (201673 / 250000) x101 := by
    exact hx100
  let x102 : ℝ := -(48327 / 250000)
  have hx102 : Bounds (-48327 / 250000) (-48327 / 250000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((48327 / 250000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (201673 / 250000) (201673 / 250000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(48327 / 250000)
  have hx104 : Bounds (201673 / 250000) (201673 / 250000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-42962669 / 200000000) (-6712917 / 31250000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-34657641381 / 200000000000) (-86644103049 / 500000000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (37604259139 / 1000000000000) (37604261141 / 1000000000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (18802129569 / 1000000000000) (18802130571 / 1000000000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (18802129569 / 1000000000000) (18802130571 / 1000000000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-18802130571 / 1000000000000) (-18802129569 / 1000000000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (674345049429 / 1000000000000) (674345051431 / 1000000000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (674345049429 / 1000000000000) (674345051431 / 1000000000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (48327 / 250000)
  have hx114 : Bounds (674345049429 / 1000000000000) (674345051431 / 1000000000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(96813 / 500000)
  have hx116 : Bounds (596813 / 500000) (596813 / 500000) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((96813 / 500000) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(96813 / 500000)
  have hx117 : Bounds (596813 / 500000) (596813 / 500000) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((96813 / 500000) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (176995733 / 1000000000) (88497867 / 500000000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (211266708797 / 1000000000000) (26408338749 / 125000000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(96813 / 500000)
  have hx120 : Bounds (-96813 / 500000) (-96813 / 500000) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((96813 / 500000) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (403187 / 500000) (403187 / 500000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(96813 / 500000)
  have hx122 : Bounds (403187 / 500000) (403187 / 500000) x122 := by
    exact hx121
  let x123 : ℝ := -(96813 / 500000)
  have hx123 : Bounds (-96813 / 500000) (-96813 / 500000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((96813 / 500000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (403187 / 500000) (403187 / 500000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(96813 / 500000)
  have hx125 : Bounds (403187 / 500000) (403187 / 500000) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-1721661 / 8000000) (-26900953 / 125000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-86768916701 / 500000000000) (-34707566519 / 200000000000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (7545775079 / 200000000000) (37728877397 / 1000000000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (18864437697 / 1000000000000) (18864438699 / 1000000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (18864437697 / 1000000000000) (18864438699 / 1000000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-18864438699 / 1000000000000) (-18864437697 / 1000000000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (674282741301 / 1000000000000) (674282743303 / 1000000000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (674282741301 / 1000000000000) (674282743303 / 1000000000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (96813 / 500000)
  have hx135 : Bounds (674282741301 / 1000000000000) (674282743303 / 1000000000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(48327 / 250000)
  have hx136 : Bounds (673176892517 / 1000000000000) (337171799281 / 500000000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((48327 / 250000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(96813 / 500000)
  have hx137 : Bounds (674284297549 / 1000000000000) (5403623383 / 8000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((96813 / 500000) : ℝ)) <;> norm_num
  let c : ℝ := doubleCapHighTailC x
  have hcMem := Reflection.regularContact_mem
    (x / (Real.log 2 * doubleCapHighTailFloor x))
  have hc0 : 0 ≤ c := by
    dsimp only [c, doubleCapHighTailC]
    apply GeneralCK.Certificates.RegularContactBounds.regularContact_nonneg
    exact div_nonneg hxPos0.le ((mul_pos log_two_pos hh0).le)
  have hcEq : biasE c = x93 * c := by
    have he := doubleCapHighTailC_equation x
    change c = (x / (Real.log 2 * doubleCapHighTailFloor x)) * biasE c at he
    rw [hEll'] at he
    have hxPos : 0 < x := hxPos0
    have hEllPos : 0 < x48 := by rw [← hEll']; exact mul_pos log_two_pos hh0
    change biasE c = (x48 / x) * c
    field_simp [hxPos.ne', hEllPos.ne'] at he ⊢
    nlinarith
  have hc : Bounds (48327 / 250000) (96813 / 500000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num)
      (by norm_num) (show 0 < x93 by linarith [hx93.1]) hcEq
    · have h1 : x93 * (48327 / 250000) ≤ (337171799281 / 500000000000) := hx136.2
      have h2 : (674345049429 / 1000000000000) ≤ biasE (48327 / 250000) := hx114.1
      linarith
    · have h1 : biasE (96813 / 500000) ≤ (674282743303 / 1000000000000) := hx135.2
      have h2 : (674284297549 / 1000000000000) ≤ x93 * (96813 / 500000) := hx137.1
      linarith
  let x138 : ℝ := (1 / 1)+x0
  have hx138 : Bounds (881 / 640) (7051 / 5120) x138 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx0 <;> norm_num
  let x139 : ℝ := -x0
  have hx139 : Bounds (-1931 / 5120) (-241 / 640) x139 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x140 : ℝ := (1 / 1)+x139
  have hx140 : Bounds (3189 / 5120) (399 / 640) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx139 <;> norm_num
  let x141 : ℝ := (1 / 1)-x0
  have hx141 : Bounds (3189 / 5120) (399 / 640) x141 := by
    exact hx140
  let x142 : ℝ := x141⁻¹
  have hx142 : Bounds (802005012531 / 500000000000) (321103794293 / 200000000000) x142 := by
    apply bounds_inv hx141 <;> norm_num
  let x143 : ℝ := x138*x142
  have hx143 : Bounds (552005012531 / 250000000000) (221103794293 / 100000000000) x143 := by
    apply bounds_mul hx138 hx142 <;> norm_num
  let x144 : ℝ := x138/x141
  have hx144 : Bounds (552005012531 / 250000000000) (221103794293 / 100000000000) x144 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx143
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (49506013 / 62500000) (49591379 / 62500000) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_14.2)
  let x146 : ℝ := (2 / 1)⁻¹
  have hx146 : Bounds (1 / 2) (1 / 2) x146 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x147 : ℝ := x145*x146
  have hx147 : Bounds (49506013 / 125000000) (49591379 / 125000000) x147 := by
    apply bounds_mul hx145 hx146 <;> norm_num
  let x148 : ℝ := x145/(2 / 1)
  have hx148 : Bounds (49506013 / 125000000) (49591379 / 125000000) x148 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx147
  let x149 : ℝ := (1 / 1)+y
  have hx149 : Bounds (1267943 / 1000000) (634183 / 500000) x149 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x150 : ℝ := -y
  have hx150 : Bounds (-134183 / 500000) (-267943 / 1000000) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (365817 / 500000) (732057 / 1000000) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-y
  have hx152 : Bounds (365817 / 500000) (732057 / 1000000) x152 := by
    exact hx151
  let x153 : ℝ := x152⁻¹
  have hx153 : Bounds (170751731081 / 125000000000) (136680362039 / 100000000000) x153 := by
    apply bounds_inv hx152 <;> norm_num
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (108251731081 / 62500000000) (86680362039 / 50000000000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x149/x152
  have hx155 : Bounds (108251731081 / 62500000000) (86680362039 / 50000000000) x155 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx154
  let x156 : ℝ := Real.log x155
  have hx156 : Bounds (549292801 / 1000000000) (137551087 / 250000000) x156 := by
    exact bounds_log hx155 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_16.2)
  let x157 : ℝ := (2 / 1)⁻¹
  have hx157 : Bounds (1 / 2) (1 / 2) x157 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x158 : ℝ := x156*x157
  have hx158 : Bounds (549292801 / 2000000000) (137551087 / 500000000) x158 := by
    apply bounds_mul hx156 hx157 <;> norm_num
  let x159 : ℝ := x156/(2 / 1)
  have hx159 : Bounds (549292801 / 2000000000) (137551087 / 500000000) x159 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx158
  let x160 : ℝ := (1 / 1)+c
  have hx160 : Bounds (298327 / 250000) (596813 / 500000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x161 : ℝ := -c
  have hx161 : Bounds (-96813 / 500000) (-48327 / 250000) x161 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x162 : ℝ := (1 / 1)+x161
  have hx162 : Bounds (403187 / 500000) (201673 / 250000) x162 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx161 <;> norm_num
  let x163 : ℝ := (1 / 1)-c
  have hx163 : Bounds (403187 / 500000) (201673 / 250000) x163 := by
    exact hx162
  let x164 : ℝ := x163⁻¹
  have hx164 : Bounds (1239630490943 / 1000000000000) (1240119349087 / 1000000000000) x164 := by
    apply bounds_inv hx163 <;> norm_num
  let x165 : ℝ := x160*x164
  have hx165 : Bounds (739630490943 / 500000000000) (740119349087 / 500000000000) x165 := by
    apply bounds_mul hx160 hx164 <;> norm_num
  let x166 : ℝ := x160/x163
  have hx166 : Bounds (739630490943 / 500000000000) (740119349087 / 500000000000) x166 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx165
  let x167 : ℝ := Real.log x166
  have hx167 : Bounds (195771313 / 500000000) (196101679 / 500000000) x167 := by
    exact bounds_log hx166 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x168 : ℝ := (2 / 1)⁻¹
  have hx168 : Bounds (1 / 2) (1 / 2) x168 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x169 : ℝ := x167*x168
  have hx169 : Bounds (195771313 / 1000000000) (196101679 / 1000000000) x169 := by
    apply bounds_mul hx167 hx168 <;> norm_num
  let x170 : ℝ := x167/(2 / 1)
  have hx170 : Bounds (195771313 / 1000000000) (196101679 / 1000000000) x170 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx169
  let x171 : ℝ := Real.log (2 / 1)
  have hx171 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x171 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x172 : ℝ := c*c
  have hx172 : Bounds (2335498929 / 62500000000) (9372756969 / 250000000000) x172 := by
    apply bounds_mul hc hc <;> norm_num
  let x173 : ℝ := -x172
  have hx173 : Bounds (-9372756969 / 250000000000) (-2335498929 / 62500000000) x173 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx172
  let x174 : ℝ := (1 / 1)+x173
  have hx174 : Bounds (240627243031 / 250000000000) (60164501071 / 62500000000) x174 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx173 <;> norm_num
  let x175 : ℝ := (1 / 1)-x172
  have hx175 : Bounds (240627243031 / 250000000000) (60164501071 / 62500000000) x175 := by
    exact hx174
  let x176 : ℝ := Real.log x175
  have hx176 : Bounds (-9552973 / 250000000) (-38084061 / 1000000000) x176 := by
    exact bounds_log hx175 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (-9552973 / 500000000) (-38084061 / 2000000000) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (-9552973 / 500000000) (-38084061 / 2000000000) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (38084061 / 2000000000) (9552973 / 500000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x171+x180
  have hx181 : Bounds (1424378421 / 2000000000) (712253127 / 1000000000) x181 := by
    apply bounds_add hx171 hx180 <;> norm_num
  let x182 : ℝ := x171-x179
  have hx182 : Bounds (1424378421 / 2000000000) (712253127 / 1000000000) x182 := by
    exact hx181
  let x183 : ℝ := Real.log (2 / 1)
  have hx183 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x183 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x184 : ℝ := (1 / 1)+(96813 / 500000)
  have hx184 : Bounds (596813 / 500000) (596813 / 500000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((96813 / 500000) : ℝ)) <;> norm_num
  let x185 : ℝ := (1 / 1)+(96813 / 500000)
  have hx185 : Bounds (596813 / 500000) (596813 / 500000) x185 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((96813 / 500000) : ℝ)) <;> norm_num
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (176995733 / 1000000000) (88497867 / 500000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x187 : ℝ := x184*x186
  have hx187 : Bounds (211266708797 / 1000000000000) (26408338749 / 125000000000) x187 := by
    apply bounds_mul hx184 hx186 <;> norm_num
  let x188 : ℝ := -(96813 / 500000)
  have hx188 : Bounds (-96813 / 500000) (-96813 / 500000) x188 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((96813 / 500000) : ℝ))
  let x189 : ℝ := (1 / 1)+x188
  have hx189 : Bounds (403187 / 500000) (403187 / 500000) x189 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx188 <;> norm_num
  let x190 : ℝ := (1 / 1)-(96813 / 500000)
  have hx190 : Bounds (403187 / 500000) (403187 / 500000) x190 := by
    exact hx189
  let x191 : ℝ := -(96813 / 500000)
  have hx191 : Bounds (-96813 / 500000) (-96813 / 500000) x191 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((96813 / 500000) : ℝ))
  let x192 : ℝ := (1 / 1)+x191
  have hx192 : Bounds (403187 / 500000) (403187 / 500000) x192 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx191 <;> norm_num
  let x193 : ℝ := (1 / 1)-(96813 / 500000)
  have hx193 : Bounds (403187 / 500000) (403187 / 500000) x193 := by
    exact hx192
  let x194 : ℝ := Real.log x193
  have hx194 : Bounds (-1721661 / 8000000) (-26900953 / 125000000) x194 := by
    exact bounds_log hx193 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x195 : ℝ := x190*x194
  have hx195 : Bounds (-86768916701 / 500000000000) (-34707566519 / 200000000000) x195 := by
    apply bounds_mul hx190 hx194 <;> norm_num
  let x196 : ℝ := x187+x195
  have hx196 : Bounds (7545775079 / 200000000000) (37728877397 / 1000000000000) x196 := by
    apply bounds_add hx187 hx195 <;> norm_num
  let x197 : ℝ := (2 / 1)⁻¹
  have hx197 : Bounds (1 / 2) (1 / 2) x197 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x198 : ℝ := x196*x197
  have hx198 : Bounds (18864437697 / 1000000000000) (18864438699 / 1000000000000) x198 := by
    apply bounds_mul hx196 hx197 <;> norm_num
  let x199 : ℝ := x196/(2 / 1)
  have hx199 : Bounds (18864437697 / 1000000000000) (18864438699 / 1000000000000) x199 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx198
  let x200 : ℝ := -x199
  have hx200 : Bounds (-18864438699 / 1000000000000) (-18864437697 / 1000000000000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx199
  let x201 : ℝ := x183+x200
  have hx201 : Bounds (674282741301 / 1000000000000) (674282743303 / 1000000000000) x201 := by
    apply bounds_add hx183 hx200 <;> norm_num
  let x202 : ℝ := x183-x199
  have hx202 : Bounds (674282741301 / 1000000000000) (674282743303 / 1000000000000) x202 := by
    exact hx201
  let x203 : ℝ := biasE (96813 / 500000)
  have hx203 : Bounds (674282741301 / 1000000000000) (674282743303 / 1000000000000) x203 := by
    simpa +zetaDelta only [biasE, div_one] using hx202
  let x204 : ℝ := Real.log (2 / 1)
  have hx204 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x204 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x205 : ℝ := (1 / 1)+(48327 / 250000)
  have hx205 : Bounds (298327 / 250000) (298327 / 250000) x205 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((48327 / 250000) : ℝ)) <;> norm_num
  let x206 : ℝ := (1 / 1)+(48327 / 250000)
  have hx206 : Bounds (298327 / 250000) (298327 / 250000) x206 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((48327 / 250000) : ℝ)) <;> norm_num
  let x207 : ℝ := Real.log x206
  have hx207 : Bounds (88364641 / 500000000) (176729283 / 1000000000) x207 := by
    exact bounds_log hx206 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x208 : ℝ := x205*x207
  have hx208 : Bounds (52723116511 / 250000000000) (210892467239 / 1000000000000) x208 := by
    apply bounds_mul hx205 hx207 <;> norm_num
  let x209 : ℝ := -(48327 / 250000)
  have hx209 : Bounds (-48327 / 250000) (-48327 / 250000) x209 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((48327 / 250000) : ℝ))
  let x210 : ℝ := (1 / 1)+x209
  have hx210 : Bounds (201673 / 250000) (201673 / 250000) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx209 <;> norm_num
  let x211 : ℝ := (1 / 1)-(48327 / 250000)
  have hx211 : Bounds (201673 / 250000) (201673 / 250000) x211 := by
    exact hx210
  let x212 : ℝ := -(48327 / 250000)
  have hx212 : Bounds (-48327 / 250000) (-48327 / 250000) x212 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((48327 / 250000) : ℝ))
  let x213 : ℝ := (1 / 1)+x212
  have hx213 : Bounds (201673 / 250000) (201673 / 250000) x213 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx212 <;> norm_num
  let x214 : ℝ := (1 / 1)-(48327 / 250000)
  have hx214 : Bounds (201673 / 250000) (201673 / 250000) x214 := by
    exact hx213
  let x215 : ℝ := Real.log x214
  have hx215 : Bounds (-42962669 / 200000000) (-6712917 / 31250000) x215 := by
    exact bounds_log hx214 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x216 : ℝ := x211*x215
  have hx216 : Bounds (-34657641381 / 200000000000) (-86644103049 / 500000000000) x216 := by
    apply bounds_mul hx211 hx215 <;> norm_num
  let x217 : ℝ := x208+x216
  have hx217 : Bounds (37604259139 / 1000000000000) (37604261141 / 1000000000000) x217 := by
    apply bounds_add hx208 hx216 <;> norm_num
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (18802129569 / 1000000000000) (18802130571 / 1000000000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (18802129569 / 1000000000000) (18802130571 / 1000000000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := -x220
  have hx221 : Bounds (-18802130571 / 1000000000000) (-18802129569 / 1000000000000) x221 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx220
  let x222 : ℝ := x204+x221
  have hx222 : Bounds (674345049429 / 1000000000000) (674345051431 / 1000000000000) x222 := by
    apply bounds_add hx204 hx221 <;> norm_num
  let x223 : ℝ := x204-x220
  have hx223 : Bounds (674345049429 / 1000000000000) (674345051431 / 1000000000000) x223 := by
    exact hx222
  let x224 : ℝ := biasE (48327 / 250000)
  have hx224 : Bounds (674345049429 / 1000000000000) (674345051431 / 1000000000000) x224 := by
    simpa +zetaDelta only [biasE, div_one] using hx223
  let x225 : ℝ := biasE c
  have hx225 : Bounds (674282741301 / 1000000000000) (674345051431 / 1000000000000) x225 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx203.1 hx224.2
  let x226 : ℝ := x159⁻¹
  have hx226 : Bounds (727002615399 / 200000000000) (3641045352059 / 1000000000000) x226 := by
    apply bounds_inv hx159 <;> norm_num
  let x227 : ℝ := x148*x226
  have hx227 : Bounds (1439640037159 / 1000000000000) (722257840041 / 500000000000) x227 := by
    apply bounds_mul hx148 hx226 <;> norm_num
  let x228 : ℝ := x148/x159
  have hx228 : Bounds (1439640037159 / 1000000000000) (722257840041 / 500000000000) x228 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx227
  let x229 : ℝ := c*x148
  have hx229 : Bounds (9569908361 / 125000000000) (76817442803 / 1000000000000) x229 := by
    apply bounds_mul hc hx148 <;> norm_num
  let x230 : ℝ := x225+x229
  have hx230 : Bounds (750842008189 / 1000000000000) (375581247117 / 500000000000) x230 := by
    apply bounds_add hx225 hx229 <;> norm_num
  let x231 : ℝ := x*x170
  have hx231 : Bounds (1474402701 / 40000000000) (36979720913 / 1000000000000) x231 := by
    apply bounds_mul hx hx170 <;> norm_num
  let x232 : ℝ := x48+x231
  have hx232 : Bounds (138710402591 / 200000000000) (43361737343 / 62500000000) x232 := by
    apply bounds_add hx48 hx231 <;> norm_num
  let x233 : ℝ := x232⁻¹
  have hx233 : Bounds (1441362911859 / 1000000000000) (45057903973 / 31250000000) x233 := by
    apply bounds_inv hx232 <;> norm_num
  let x234 : ℝ := x230*x233
  have hx234 : Bounds (1082235823269 / 1000000000000) (1083065841067 / 1000000000000) x234 := by
    apply bounds_mul hx230 hx233 <;> norm_num
  let x235 : ℝ := x230/x232
  have hx235 : Bounds (1082235823269 / 1000000000000) (1083065841067 / 1000000000000) x235 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx234
  let x236 : ℝ := y*y
  have hx236 : Bounds (71793451249 / 1000000000000) (18005077489 / 250000000000) x236 := by
    apply bounds_mul hy hy <;> norm_num
  let x237 : ℝ := -x236
  have hx237 : Bounds (-18005077489 / 250000000000) (-71793451249 / 1000000000000) x237 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx236
  let x238 : ℝ := (1 / 1)+x237
  have hx238 : Bounds (231994922511 / 250000000000) (928206548751 / 1000000000000) x238 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx237 <;> norm_num
  let x239 : ℝ := (1 / 1)-x236
  have hx239 : Bounds (231994922511 / 250000000000) (928206548751 / 1000000000000) x239 := by
    exact hx238
  let x240 : ℝ := x239*x159
  have hx240 : Bounds (254866281607 / 1000000000000) (255351639483 / 1000000000000) x240 := by
    apply bounds_mul hx239 hx159 <;> norm_num
  let x241 : ℝ := c*c
  have hx241 : Bounds (2335498929 / 62500000000) (9372756969 / 250000000000) x241 := by
    apply bounds_mul hc hc <;> norm_num
  let x242 : ℝ := -x241
  have hx242 : Bounds (-9372756969 / 250000000000) (-2335498929 / 62500000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx241
  let x243 : ℝ := (1 / 1)+x242
  have hx243 : Bounds (240627243031 / 250000000000) (60164501071 / 62500000000) x243 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx242 <;> norm_num
  let x244 : ℝ := (1 / 1)-x241
  have hx244 : Bounds (240627243031 / 250000000000) (60164501071 / 62500000000) x244 := by
    exact hx243
  let x245 : ℝ := x244*x182
  have hx245 : Bounds (171372126239 / 250000000000) (171409416089 / 250000000000) x245 := by
    apply bounds_mul hx244 hx182 <;> norm_num
  let x246 : ℝ := y*y
  have hx246 : Bounds (71793451249 / 1000000000000) (18005077489 / 250000000000) x246 := by
    apply bounds_mul hy hy <;> norm_num
  let x247 : ℝ := (1 / 1)+x246
  have hx247 : Bounds (1071793451249 / 1000000000000) (268005077489 / 250000000000) x247 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx246 <;> norm_num
  let x248 : ℝ := x247*x159
  have hx248 : Bounds (58872842693 / 200000000000) (147457558921 / 500000000000) x248 := by
    apply bounds_mul hx247 hx159 <;> norm_num
  let x249 : ℝ := -y
  have hx249 : Bounds (-134183 / 500000) (-267943 / 1000000) x249 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x250 : ℝ := x248+x249
  have hx250 : Bounds (5199642693 / 200000000000) (13486058921 / 500000000000) x250 := by
    apply bounds_add hx248 hx249 <;> norm_num
  let x251 : ℝ := x248-y
  have hx251 : Bounds (5199642693 / 200000000000) (13486058921 / 500000000000) x251 := by
    exact hx250
  let x252 : ℝ := x240*x240
  have hx252 : Bounds (129913643 / 2000000000) (65204459787 / 1000000000000) x252 := by
    apply bounds_mul hx240 hx240 <;> norm_num
  let x253 : ℝ := x252⁻¹
  have hx253 : Bounds (7668187139857 / 500000000000) (7697420970637 / 500000000000) x253 := by
    apply bounds_inv hx252 <;> norm_num
  let x254 : ℝ := x251*x253
  have hx254 : Bounds (398718332303 / 1000000000000) (415231491 / 1000000000) x254 := by
    apply bounds_mul hx251 hx253 <;> norm_num
  let x255 : ℝ := x251/x252
  have hx255 : Bounds (398718332303 / 1000000000000) (415231491 / 1000000000) x255 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx254
  let x256 : ℝ := (-2 / 1)*x255
  have hx256 : Bounds (-415231491 / 500000000) (-398718332303 / 500000000000) x256 := by
    apply bounds_mul (bounds_const ((-2 / 1) : ℝ)) hx255 <;> norm_num
  let x257 : ℝ := x256*x228
  have hx257 : Bounds (-1199616799227 / 1000000000000) (-229604349893 / 200000000000) x257 := by
    apply bounds_mul hx256 hx228 <;> norm_num
  let x258 : ℝ := (2 / 1)*x182
  have hx258 : Bounds (1424378421 / 1000000000) (712253127 / 500000000) x258 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx182 <;> norm_num
  let x259 : ℝ := c*c
  have hx259 : Bounds (2335498929 / 62500000000) (9372756969 / 250000000000) x259 := by
    apply bounds_mul hc hc <;> norm_num
  let x260 : ℝ := -x259
  have hx260 : Bounds (-9372756969 / 250000000000) (-2335498929 / 62500000000) x260 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx259
  let x261 : ℝ := x258+x260
  have hx261 : Bounds (346721848281 / 250000000000) (43348070973 / 31250000000) x261 := by
    apply bounds_add hx258 hx260 <;> norm_num
  let x262 : ℝ := x258-x259
  have hx262 : Bounds (346721848281 / 250000000000) (43348070973 / 31250000000) x262 := by
    exact hx261
  let x263 : ℝ := c*x262
  have hx263 : Bounds (26809642819 / 100000000000) (268586034887 / 1000000000000) x263 := by
    apply bounds_mul hc hx262 <;> norm_num
  let x264 : ℝ := x245*x245
  have hx264 : Bounds (234947245213 / 500000000000) (7345296981 / 15625000000) x264 := by
    apply bounds_mul hx245 hx245 <;> norm_num
  let x265 : ℝ := x264⁻¹
  have hx265 : Bounds (53180286789 / 25000000000) (266017164591 / 125000000000) x265 := by
    apply bounds_inv hx264 <;> norm_num
  let x266 : ℝ := x263*x265
  have hx266 : Bounds (57029779753 / 100000000000) (142896990899 / 250000000000) x266 := by
    apply bounds_mul hx263 hx265 <;> norm_num
  let x267 : ℝ := x263/x264
  have hx267 : Bounds (57029779753 / 100000000000) (142896990899 / 250000000000) x267 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx266
  let x268 : ℝ := (2 / 1)*x267
  have hx268 : Bounds (57029779753 / 50000000000) (142896990899 / 125000000000) x268 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx267 <;> norm_num
  let x269 : ℝ := x268*x235
  have hx269 : Bounds (308598353209 / 250000000000) (77383424817 / 62500000000) x269 := by
    apply bounds_mul hx268 hx235 <;> norm_num
  let x270 : ℝ := x257+x269
  have hx270 : Bounds (34776613609 / 1000000000000) (90113047607 / 1000000000000) x270 := by
    apply bounds_add hx257 hx269 <;> norm_num
  have hPos : 0 < x270 :=
    lt_of_lt_of_le (by norm_num) hx270.1
  have hBridgeL : doubleCapBridgeL x = x48 := by
    exact hEll'
  rw [← doubleCapBridgeDerivativeTraceForm_eq x]
  simpa +zetaDelta only [doubleCapBridgeDerivativeTraceForm,
    hBridgeL, SmallMean.A, biasB, div_one, pow_two] using hPos

theorem acceptedCell : DoubleCapBridgeDerivativeCellCertificate
    (⟨216, by decide⟩ : Fin 256) doubleCapBridgeDerivativeExpression where
  positive x hx := by
    have hloEq : doubleCapBridgeLo (⟨216, by decide⟩ : Fin 256) =
        (241 / 1280) := by norm_num [doubleCapBridgeLo, doubleCapBridgeStep]
    have hhiEq : doubleCapBridgeHi (⟨216, by decide⟩ : Fin 256) =
        (1931 / 10240) := by norm_num [doubleCapBridgeHi, doubleCapBridgeStep]
    have hlo : (241 / 1280) ≤ x := by
      simpa only [hloEq] using hx.1
    have hhi : x ≤ (1931 / 10240) := by
      simpa only [hhiEq] using hx.2
    exact cell_derivative_pos x ⟨hlo, hhi⟩

#print axioms cell_derivative_pos
#print axioms acceptedCell

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell216

end


