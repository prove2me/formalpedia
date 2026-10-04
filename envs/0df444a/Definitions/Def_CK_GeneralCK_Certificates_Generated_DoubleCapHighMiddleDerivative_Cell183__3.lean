-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell183__3
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell183__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T14:05:07.52201+00:00
-- url     : https://prove2.me/theorems/db5b9217-5d43-4028-85e9-5024498b0d75
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell183 (+2 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell184, Ge…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell183 (+2 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell184, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell185)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell183 (+2 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell184, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell185)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell183 (+2 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell184, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell185) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell183 (+2 modules: GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell184, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell185).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapHighMiddleDerivativeTraceForm
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell182Logs__7

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell183 =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell183
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_derivative_pos (x : ℝ)
    (hx : Bounds (1829 / 10240) (229 / 1280) x) :
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
  have hx0 : Bounds (1829 / 5120) (229 / 640) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx <;> norm_num
  let x1 : ℝ := Real.log (2 / 1)
  have hx1 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x1 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x2 : ℝ := Real.log (2 / 1)
  have hx2 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x2 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x3 : ℝ := (1 / 1)+(229 / 640)
  have hx3 : Bounds (869 / 640) (869 / 640) x3 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((229 / 640) : ℝ)) <;> norm_num
  let x4 : ℝ := (1 / 1)+(229 / 640)
  have hx4 : Bounds (869 / 640) (869 / 640) x4 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((229 / 640) : ℝ)) <;> norm_num
  let x5 : ℝ := Real.log x4
  have hx5 : Bounds (76468737 / 250000000) (305874949 / 1000000000) x5 := by
    exact bounds_log hx4 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x6 : ℝ := x3*x5
  have hx6 : Bounds (415320827831 / 1000000000000) (41532082919 / 100000000000) x6 := by
    apply bounds_mul hx3 hx5 <;> norm_num
  let x7 : ℝ := -(229 / 640)
  have hx7 : Bounds (-229 / 640) (-229 / 640) x7 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((229 / 640) : ℝ))
  let x8 : ℝ := (1 / 1)+x7
  have hx8 : Bounds (411 / 640) (411 / 640) x8 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx7 <;> norm_num
  let x9 : ℝ := (1 / 1)-(229 / 640)
  have hx9 : Bounds (411 / 640) (411 / 640) x9 := by
    exact hx8
  let x10 : ℝ := -(229 / 640)
  have hx10 : Bounds (-229 / 640) (-229 / 640) x10 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((229 / 640) : ℝ))
  let x11 : ℝ := (1 / 1)+x10
  have hx11 : Bounds (411 / 640) (411 / 640) x11 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx10 <;> norm_num
  let x12 : ℝ := (1 / 1)-(229 / 640)
  have hx12 : Bounds (411 / 640) (411 / 640) x12 := by
    exact hx11
  let x13 : ℝ := Real.log x12
  have hx13 : Bounds (-221437481 / 500000000) (-442874961 / 1000000000) x13 := by
    exact bounds_log hx12 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x14 : ℝ := x9*x13
  have hx14 : Bounds (-14220438233 / 50000000000) (-284408764017 / 1000000000000) x14 := by
    apply bounds_mul hx9 hx13 <;> norm_num
  let x15 : ℝ := x6+x14
  have hx15 : Bounds (130912063171 / 1000000000000) (130912065173 / 1000000000000) x15 := by
    apply bounds_add hx6 hx14 <;> norm_num
  let x16 : ℝ := (2 / 1)⁻¹
  have hx16 : Bounds (1 / 2) (1 / 2) x16 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x17 : ℝ := x15*x16
  have hx17 : Bounds (13091206317 / 200000000000) (65456032587 / 1000000000000) x17 := by
    apply bounds_mul hx15 hx16 <;> norm_num
  let x18 : ℝ := x15/(2 / 1)
  have hx18 : Bounds (13091206317 / 200000000000) (65456032587 / 1000000000000) x18 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx17
  let x19 : ℝ := -x18
  have hx19 : Bounds (-65456032587 / 1000000000000) (-13091206317 / 200000000000) x19 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx18
  let x20 : ℝ := x2+x19
  have hx20 : Bounds (627691147413 / 1000000000000) (125538229883 / 200000000000) x20 := by
    apply bounds_add hx2 hx19 <;> norm_num
  let x21 : ℝ := x2-x18
  have hx21 : Bounds (627691147413 / 1000000000000) (125538229883 / 200000000000) x21 := by
    exact hx20
  let x22 : ℝ := biasE (229 / 640)
  have hx22 : Bounds (627691147413 / 1000000000000) (125538229883 / 200000000000) x22 := by
    simpa +zetaDelta only [biasE, div_one] using hx21
  let x23 : ℝ := Real.log (2 / 1)
  have hx23 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x23 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x24 : ℝ := (1 / 1)+(1829 / 5120)
  have hx24 : Bounds (6949 / 5120) (6949 / 5120) x24 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1829 / 5120) : ℝ)) <;> norm_num
  let x25 : ℝ := (1 / 1)+(1829 / 5120)
  have hx25 : Bounds (6949 / 5120) (6949 / 5120) x25 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1829 / 5120) : ℝ)) <;> norm_num
  let x26 : ℝ := Real.log x25
  have hx26 : Bounds (12217733 / 40000000) (152721663 / 500000000) x26 := by
    exact bounds_log hx25 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x27 : ℝ := x24*x26
  have hx27 : Bounds (103638948507 / 250000000000) (207277897693 / 500000000000) x27 := by
    apply bounds_mul hx24 hx26 <;> norm_num
  let x28 : ℝ := -(1829 / 5120)
  have hx28 : Bounds (-1829 / 5120) (-1829 / 5120) x28 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1829 / 5120) : ℝ))
  let x29 : ℝ := (1 / 1)+x28
  have hx29 : Bounds (3291 / 5120) (3291 / 5120) x29 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx28 <;> norm_num
  let x30 : ℝ := (1 / 1)-(1829 / 5120)
  have hx30 : Bounds (3291 / 5120) (3291 / 5120) x30 := by
    exact hx29
  let x31 : ℝ := -(1829 / 5120)
  have hx31 : Bounds (-1829 / 5120) (-1829 / 5120) x31 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1829 / 5120) : ℝ))
  let x32 : ℝ := (1 / 1)+x31
  have hx32 : Bounds (3291 / 5120) (3291 / 5120) x32 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx31 <;> norm_num
  let x33 : ℝ := (1 / 1)-(1829 / 5120)
  have hx33 : Bounds (3291 / 5120) (3291 / 5120) x33 := by
    exact hx32
  let x34 : ℝ := Real.log x33
  have hx34 : Bounds (-44196297 / 100000000) (-441962969 / 1000000000) x34 := by
    exact bounds_log hx33 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x35 : ℝ := x30*x34
  have hx35 : Bounds (-11363282299 / 40000000000) (-284082056831 / 1000000000000) x35 := by
    apply bounds_mul hx30 hx34 <;> norm_num
  let x36 : ℝ := x27+x35
  have hx36 : Bounds (130473736553 / 1000000000000) (26094747711 / 200000000000) x36 := by
    apply bounds_add hx27 hx35 <;> norm_num
  let x37 : ℝ := (2 / 1)⁻¹
  have hx37 : Bounds (1 / 2) (1 / 2) x37 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x38 : ℝ := x36*x37
  have hx38 : Bounds (16309217069 / 250000000000) (32618434639 / 500000000000) x38 := by
    apply bounds_mul hx36 hx37 <;> norm_num
  let x39 : ℝ := x36/(2 / 1)
  have hx39 : Bounds (16309217069 / 250000000000) (32618434639 / 500000000000) x39 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx38
  let x40 : ℝ := -x39
  have hx40 : Bounds (-32618434639 / 500000000000) (-16309217069 / 250000000000) x40 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx39
  let x41 : ℝ := x23+x40
  have hx41 : Bounds (313955155361 / 500000000000) (156977578181 / 250000000000) x41 := by
    apply bounds_add hx23 hx40 <;> norm_num
  let x42 : ℝ := x23-x39
  have hx42 : Bounds (313955155361 / 500000000000) (156977578181 / 250000000000) x42 := by
    exact hx41
  let x43 : ℝ := biasE (1829 / 5120)
  have hx43 : Bounds (313955155361 / 500000000000) (156977578181 / 250000000000) x43 := by
    simpa +zetaDelta only [biasE, div_one] using hx42
  let x44 : ℝ := biasE x0
  have hx44 : Bounds (627691147413 / 1000000000000) (156977578181 / 250000000000) x44 := by
    exact bounds_biasE hx0 (by norm_num) (by norm_num) hx22.1 hx43.2
  let x45 : ℝ := x1+x44
  have hx45 : Bounds (1320838327413 / 1000000000000) (330264373431 / 250000000000) x45 := by
    apply bounds_add hx1 hx44 <;> norm_num
  let x46 : ℝ := (2 / 1)⁻¹
  have hx46 : Bounds (1 / 2) (1 / 2) x46 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x47 : ℝ := x45*x46
  have hx47 : Bounds (330209581853 / 500000000000) (330264373431 / 500000000000) x47 := by
    apply bounds_mul hx45 hx46 <;> norm_num
  let x48 : ℝ := x45/(2 / 1)
  have hx48 : Bounds (330209581853 / 500000000000) (330264373431 / 500000000000) x48 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx47
  let x49 : ℝ := Real.log (2 / 1)
  have hx49 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x49 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x50 : ℝ := (1 / 1)+(3969 / 15625)
  have hx50 : Bounds (19594 / 15625) (19594 / 15625) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((3969 / 15625) : ℝ)) <;> norm_num
  let x51 : ℝ := (1 / 1)+(3969 / 15625)
  have hx51 : Bounds (19594 / 15625) (19594 / 15625) x51 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((3969 / 15625) : ℝ)) <;> norm_num
  let x52 : ℝ := Real.log x51
  have hx52 : Bounds (226351201 / 1000000000) (113175601 / 500000000) x52 := by
    exact bounds_log hx51 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x53 : ℝ := x50*x52
  have hx53 : Bounds (283848027673 / 1000000000000) (1108781363 / 3906250000) x53 := by
    apply bounds_mul hx50 hx52 <;> norm_num
  let x54 : ℝ := -(3969 / 15625)
  have hx54 : Bounds (-3969 / 15625) (-3969 / 15625) x54 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((3969 / 15625) : ℝ))
  let x55 : ℝ := (1 / 1)+x54
  have hx55 : Bounds (11656 / 15625) (11656 / 15625) x55 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx54 <;> norm_num
  let x56 : ℝ := (1 / 1)-(3969 / 15625)
  have hx56 : Bounds (11656 / 15625) (11656 / 15625) x56 := by
    exact hx55
  let x57 : ℝ := -(3969 / 15625)
  have hx57 : Bounds (-3969 / 15625) (-3969 / 15625) x57 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((3969 / 15625) : ℝ))
  let x58 : ℝ := (1 / 1)+x57
  have hx58 : Bounds (11656 / 15625) (11656 / 15625) x58 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx57 <;> norm_num
  let x59 : ℝ := (1 / 1)-(3969 / 15625)
  have hx59 : Bounds (11656 / 15625) (11656 / 15625) x59 := by
    exact hx58
  let x60 : ℝ := Real.log x59
  have hx60 : Bounds (-293051127 / 1000000000) (-146525563 / 500000000) x60 := by
    exact bounds_log hx59 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x61 : ℝ := x56*x60
  have hx61 : Bounds (-54652862981 / 250000000000) (-218611451177 / 1000000000000) x61 := by
    apply bounds_mul hx56 hx60 <;> norm_num
  let x62 : ℝ := x53+x61
  have hx62 : Bounds (65236575749 / 1000000000000) (65236577751 / 1000000000000) x62 := by
    apply bounds_add hx53 hx61 <;> norm_num
  let x63 : ℝ := (2 / 1)⁻¹
  have hx63 : Bounds (1 / 2) (1 / 2) x63 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x64 : ℝ := x62*x63
  have hx64 : Bounds (16309143937 / 500000000000) (8154572219 / 250000000000) x64 := by
    apply bounds_mul hx62 hx63 <;> norm_num
  let x65 : ℝ := x62/(2 / 1)
  have hx65 : Bounds (16309143937 / 500000000000) (8154572219 / 250000000000) x65 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx64
  let x66 : ℝ := -x65
  have hx66 : Bounds (-8154572219 / 250000000000) (-16309143937 / 500000000000) x66 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx65
  let x67 : ℝ := x49+x66
  have hx67 : Bounds (165132222781 / 250000000000) (330264446563 / 500000000000) x67 := by
    apply bounds_add hx49 hx66 <;> norm_num
  let x68 : ℝ := x49-x65
  have hx68 : Bounds (165132222781 / 250000000000) (330264446563 / 500000000000) x68 := by
    exact hx67
  let x69 : ℝ := biasE (3969 / 15625)
  have hx69 : Bounds (165132222781 / 250000000000) (330264446563 / 500000000000) x69 := by
    simpa +zetaDelta only [biasE, div_one] using hx68
  let x70 : ℝ := Real.log (2 / 1)
  have hx70 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x70 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x71 : ℝ := (1 / 1)+(254439 / 1000000)
  have hx71 : Bounds (1254439 / 1000000) (1254439 / 1000000) x71 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((254439 / 1000000) : ℝ)) <;> norm_num
  let x72 : ℝ := (1 / 1)+(254439 / 1000000)
  have hx72 : Bounds (1254439 / 1000000) (1254439 / 1000000) x72 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((254439 / 1000000) : ℝ)) <;> norm_num
  let x73 : ℝ := Real.log x72
  have hx73 : Bounds (11334423 / 50000000) (226688461 / 1000000000) x73 := by
    exact bounds_log hx72 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x74 : ℝ := x71*x73
  have hx74 : Bounds (284366845073 / 1000000000000) (284366846329 / 1000000000000) x74 := by
    apply bounds_mul hx71 hx73 <;> norm_num
  let x75 : ℝ := -(254439 / 1000000)
  have hx75 : Bounds (-254439 / 1000000) (-254439 / 1000000) x75 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((254439 / 1000000) : ℝ))
  let x76 : ℝ := (1 / 1)+x75
  have hx76 : Bounds (745561 / 1000000) (745561 / 1000000) x76 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx75 <;> norm_num
  let x77 : ℝ := (1 / 1)-(254439 / 1000000)
  have hx77 : Bounds (745561 / 1000000) (745561 / 1000000) x77 := by
    exact hx76
  let x78 : ℝ := -(254439 / 1000000)
  have hx78 : Bounds (-254439 / 1000000) (-254439 / 1000000) x78 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((254439 / 1000000) : ℝ))
  let x79 : ℝ := (1 / 1)+x78
  have hx79 : Bounds (745561 / 1000000) (745561 / 1000000) x79 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx78 <;> norm_num
  let x80 : ℝ := (1 / 1)-(254439 / 1000000)
  have hx80 : Bounds (745561 / 1000000) (745561 / 1000000) x80 := by
    exact hx79
  let x81 : ℝ := Real.log x80
  have hx81 : Bounds (-73404581 / 250000000) (-293618323 / 1000000000) x81 := by
    exact bounds_log hx80 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x82 : ℝ := x77*x81
  have hx82 : Bounds (-10945518563 / 50000000000) (-109455185257 / 500000000000) x82 := by
    apply bounds_mul hx77 hx81 <;> norm_num
  let x83 : ℝ := x74+x82
  have hx83 : Bounds (65456473813 / 1000000000000) (13091295163 / 200000000000) x83 := by
    apply bounds_add hx74 hx82 <;> norm_num
  let x84 : ℝ := (2 / 1)⁻¹
  have hx84 : Bounds (1 / 2) (1 / 2) x84 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x85 : ℝ := x83*x84
  have hx85 : Bounds (16364118453 / 500000000000) (8182059477 / 250000000000) x85 := by
    apply bounds_mul hx83 hx84 <;> norm_num
  let x86 : ℝ := x83/(2 / 1)
  have hx86 : Bounds (16364118453 / 500000000000) (8182059477 / 250000000000) x86 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx85
  let x87 : ℝ := -x86
  have hx87 : Bounds (-8182059477 / 250000000000) (-16364118453 / 500000000000) x87 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx86
  let x88 : ℝ := x70+x87
  have hx88 : Bounds (165104735523 / 250000000000) (330209472047 / 500000000000) x88 := by
    apply bounds_add hx70 hx87 <;> norm_num
  let x89 : ℝ := x70-x86
  have hx89 : Bounds (165104735523 / 250000000000) (330209472047 / 500000000000) x89 := by
    exact hx88
  let x90 : ℝ := biasE (254439 / 1000000)
  have hx90 : Bounds (165104735523 / 250000000000) (330209472047 / 500000000000) x90 := by
    simpa +zetaDelta only [biasE, div_one] using hx89
  let y : ℝ := doubleCapHighTailY x
  have hEll' : Real.log 2 * doubleCapHighTailFloor x = x48 := by
    simpa +zetaDelta only [div_one] using hEll
  have hy : Bounds (3969 / 15625) (254439 / 1000000) y := by
    dsimp only [y, doubleCapHighTailY]
    apply entropyInverseBias_bracket hh0.le hh1.le
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (254439 / 1000000) ≤ (330209472047 / 500000000000) := hx90.2
      have h2 : (330209581853 / 500000000000) ≤ x48 := hx48.1
      linarith [hEll']
    · have h1 : x48 ≤ (330264373431 / 500000000000) := hx48.2
      have h2 : (165132222781 / 250000000000) ≤ biasE (3969 / 15625) := hx69.1
      linarith [hEll']
  let x91 : ℝ := x⁻¹
  have hx91 : Bounds (1117903930131 / 200000000000) (2799343903773 / 500000000000) x91 := by
    apply bounds_inv hx <;> norm_num
  let x92 : ℝ := x48*x91
  have hx92 : Bounds (3691425893203 / 1000000000000) (369809424159 / 100000000000) x92 := by
    apply bounds_mul hx48 hx91 <;> norm_num
  let x93 : ℝ := x48/x
  have hx93 : Bounds (3691425893203 / 1000000000000) (369809424159 / 100000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(36577 / 200000)
  have hx95 : Bounds (236577 / 200000) (236577 / 200000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((36577 / 200000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(36577 / 200000)
  have hx96 : Bounds (236577 / 200000) (236577 / 200000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((36577 / 200000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (167956369 / 1000000000) (16795637 / 100000000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (24834133693 / 125000000000) (24834133841 / 125000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(36577 / 200000)
  have hx99 : Bounds (-36577 / 200000) (-36577 / 200000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((36577 / 200000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (163423 / 200000) (163423 / 200000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(36577 / 200000)
  have hx101 : Bounds (163423 / 200000) (163423 / 200000) x101 := by
    exact hx100
  let x102 : ℝ := -(36577 / 200000)
  have hx102 : Bounds (-36577 / 200000) (-36577 / 200000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((36577 / 200000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (163423 / 200000) (163423 / 200000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(36577 / 200000)
  have hx104 : Bounds (163423 / 200000) (163423 / 200000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-50493859 / 250000000) (-40395087 / 200000000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-41259289597 / 250000000000) (-16503715757 / 100000000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (8408977789 / 250000000000) (16817956579 / 500000000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (8408977789 / 500000000000) (16817956579 / 1000000000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (8408977789 / 500000000000) (16817956579 / 1000000000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-16817956579 / 1000000000000) (-8408977789 / 500000000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (676329223421 / 1000000000000) (338164612711 / 500000000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (676329223421 / 1000000000000) (338164612711 / 500000000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (36577 / 200000)
  have hx114 : Bounds (676329223421 / 1000000000000) (338164612711 / 500000000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(183201 / 1000000)
  have hx116 : Bounds (1183201 / 1000000) (1183201 / 1000000) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((183201 / 1000000) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(183201 / 1000000)
  have hx117 : Bounds (1183201 / 1000000) (1183201 / 1000000) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((183201 / 1000000) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (168223477 / 1000000000) (84111739 / 500000000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (199042186209 / 1000000000000) (99521093697 / 500000000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(183201 / 1000000)
  have hx120 : Bounds (-183201 / 1000000) (-183201 / 1000000) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((183201 / 1000000) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (816799 / 1000000) (816799 / 1000000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(183201 / 1000000)
  have hx122 : Bounds (816799 / 1000000) (816799 / 1000000) x122 := by
    exact hx121
  let x123 : ℝ := -(183201 / 1000000)
  have hx123 : Bounds (-183201 / 1000000) (-183201 / 1000000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((183201 / 1000000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (816799 / 1000000) (816799 / 1000000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(183201 / 1000000)
  have hx125 : Bounds (816799 / 1000000) (816799 / 1000000) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-202362237 / 1000000000) (-50590559 / 250000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-8264463641 / 50000000000) (-82644636001 / 500000000000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (33752913389 / 1000000000000) (527389303 / 15625000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (8438228347 / 500000000000) (527389303 / 31250000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (8438228347 / 500000000000) (527389303 / 31250000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-527389303 / 31250000000) (-8438228347 / 500000000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (2641682509 / 3906250000) (338135362153 / 500000000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (2641682509 / 3906250000) (338135362153 / 500000000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (183201 / 1000000)
  have hx135 : Bounds (2641682509 / 3906250000) (338135362153 / 500000000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(36577 / 200000)
  have hx136 : Bounds (337553212239 / 500000000000) (338162982687 / 500000000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((36577 / 200000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(183201 / 1000000)
  have hx137 : Bounds (33813645753 / 50000000000) (338747281577 / 500000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((183201 / 1000000) : ℝ)) <;> norm_num
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
  have hc : Bounds (36577 / 200000) (183201 / 1000000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num)
      (by norm_num) (show 0 < x93 by linarith [hx93.1]) hcEq
    · have h1 : x93 * (36577 / 200000) ≤ (338162982687 / 500000000000) := hx136.2
      have h2 : (676329223421 / 1000000000000) ≤ biasE (36577 / 200000) := hx114.1
      linarith
    · have h1 : biasE (183201 / 1000000) ≤ (338135362153 / 500000000000) := hx135.2
      have h2 : (33813645753 / 50000000000) ≤ x93 * (183201 / 1000000) := hx137.1
      linarith
  let x138 : ℝ := (1 / 1)+x0
  have hx138 : Bounds (6949 / 5120) (869 / 640) x138 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx0 <;> norm_num
  let x139 : ℝ := -x0
  have hx139 : Bounds (-229 / 640) (-1829 / 5120) x139 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x140 : ℝ := (1 / 1)+x139
  have hx140 : Bounds (411 / 640) (3291 / 5120) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx139 <;> norm_num
  let x141 : ℝ := (1 / 1)-x0
  have hx141 : Bounds (411 / 640) (3291 / 5120) x141 := by
    exact hx140
  let x142 : ℝ := x141⁻¹
  have hx142 : Bounds (388939532057 / 250000000000) (389294403893 / 250000000000) x142 := by
    apply bounds_inv hx141 <;> norm_num
  let x143 : ℝ := x138*x142
  have hx143 : Bounds (263939532057 / 125000000000) (264294403893 / 125000000000) x143 := by
    apply bounds_mul hx138 hx142 <;> norm_num
  let x144 : ℝ := x138/x141
  have hx144 : Bounds (263939532057 / 125000000000) (264294403893 / 125000000000) x144 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx143
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (747406293 / 1000000000) (93593739 / 125000000) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_14.2)
  let x146 : ℝ := (2 / 1)⁻¹
  have hx146 : Bounds (1 / 2) (1 / 2) x146 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x147 : ℝ := x145*x146
  have hx147 : Bounds (747406293 / 2000000000) (93593739 / 250000000) x147 := by
    apply bounds_mul hx145 hx146 <;> norm_num
  let x148 : ℝ := x145/(2 / 1)
  have hx148 : Bounds (747406293 / 2000000000) (93593739 / 250000000) x148 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx147
  let x149 : ℝ := (1 / 1)+y
  have hx149 : Bounds (19594 / 15625) (1254439 / 1000000) x149 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x150 : ℝ := -y
  have hx150 : Bounds (-254439 / 1000000) (-3969 / 15625) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (745561 / 1000000) (11656 / 15625) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-y
  have hx152 : Bounds (745561 / 1000000) (11656 / 15625) x152 := by
    exact hx151
  let x153 : ℝ := x152⁻¹
  have hx153 : Bounds (1340511324639 / 1000000000000) (335317968617 / 250000000000) x153 := by
    apply bounds_inv hx152 <;> norm_num
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (840511324639 / 500000000000) (210317968617 / 125000000000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x149/x152
  have hx155 : Bounds (840511324639 / 500000000000) (210317968617 / 125000000000) x155 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx154
  let x156 : ℝ := Real.log x155
  have hx156 : Bounds (64925291 / 125000000) (104061357 / 200000000) x156 := by
    exact bounds_log hx155 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_16.2)
  let x157 : ℝ := (2 / 1)⁻¹
  have hx157 : Bounds (1 / 2) (1 / 2) x157 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x158 : ℝ := x156*x157
  have hx158 : Bounds (64925291 / 250000000) (104061357 / 400000000) x158 := by
    apply bounds_mul hx156 hx157 <;> norm_num
  let x159 : ℝ := x156/(2 / 1)
  have hx159 : Bounds (64925291 / 250000000) (104061357 / 400000000) x159 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx158
  let x160 : ℝ := (1 / 1)+c
  have hx160 : Bounds (236577 / 200000) (1183201 / 1000000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x161 : ℝ := -c
  have hx161 : Bounds (-183201 / 1000000) (-36577 / 200000) x161 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x162 : ℝ := (1 / 1)+x161
  have hx162 : Bounds (816799 / 1000000) (163423 / 200000) x162 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx161 <;> norm_num
  let x163 : ℝ := (1 / 1)-c
  have hx163 : Bounds (816799 / 1000000) (163423 / 200000) x163 := by
    exact hx162
  let x164 : ℝ := x163⁻¹
  have hx164 : Bounds (611908972421 / 500000000000) (1224291410739 / 1000000000000) x164 := by
    apply bounds_inv hx163 <;> norm_num
  let x165 : ℝ := x160*x164
  have hx165 : Bounds (361908972421 / 250000000000) (724291410739 / 500000000000) x165 := by
    apply bounds_mul hx160 hx164 <;> norm_num
  let x166 : ℝ := x160/x163
  have hx166 : Bounds (361908972421 / 250000000000) (724291410739 / 500000000000) x166 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx165
  let x167 : ℝ := Real.log x166
  have hx167 : Bounds (92482951 / 250000000) (74117143 / 200000000) x167 := by
    exact bounds_log hx166 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x168 : ℝ := (2 / 1)⁻¹
  have hx168 : Bounds (1 / 2) (1 / 2) x168 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x169 : ℝ := x167*x168
  have hx169 : Bounds (92482951 / 500000000) (74117143 / 400000000) x169 := by
    apply bounds_mul hx167 hx168 <;> norm_num
  let x170 : ℝ := x167/(2 / 1)
  have hx170 : Bounds (92482951 / 500000000) (74117143 / 400000000) x170 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx169
  let x171 : ℝ := Real.log (2 / 1)
  have hx171 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x171 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x172 : ℝ := c*c
  have hx172 : Bounds (1337876929 / 40000000000) (33562606401 / 1000000000000) x172 := by
    apply bounds_mul hc hc <;> norm_num
  let x173 : ℝ := -x172
  have hx173 : Bounds (-33562606401 / 1000000000000) (-1337876929 / 40000000000) x173 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx172
  let x174 : ℝ := (1 / 1)+x173
  have hx174 : Bounds (966437393599 / 1000000000000) (38662123071 / 40000000000) x174 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx173 <;> norm_num
  let x175 : ℝ := (1 / 1)-x172
  have hx175 : Bounds (966437393599 / 1000000000000) (38662123071 / 40000000000) x175 := by
    exact hx174
  let x176 : ℝ := Real.log x175
  have hx176 : Bounds (-34138759 / 1000000000) (-6803813 / 200000000) x176 := by
    exact bounds_log hx175 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (-34138759 / 2000000000) (-6803813 / 400000000) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (-34138759 / 2000000000) (-6803813 / 400000000) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (6803813 / 400000000) (34138759 / 2000000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x171+x180
  have hx181 : Bounds (56812537 / 80000000) (1420433121 / 2000000000) x181 := by
    apply bounds_add hx171 hx180 <;> norm_num
  let x182 : ℝ := x171-x179
  have hx182 : Bounds (56812537 / 80000000) (1420433121 / 2000000000) x182 := by
    exact hx181
  let x183 : ℝ := Real.log (2 / 1)
  have hx183 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x183 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x184 : ℝ := (1 / 1)+(183201 / 1000000)
  have hx184 : Bounds (1183201 / 1000000) (1183201 / 1000000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((183201 / 1000000) : ℝ)) <;> norm_num
  let x185 : ℝ := (1 / 1)+(183201 / 1000000)
  have hx185 : Bounds (1183201 / 1000000) (1183201 / 1000000) x185 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((183201 / 1000000) : ℝ)) <;> norm_num
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (168223477 / 1000000000) (84111739 / 500000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x187 : ℝ := x184*x186
  have hx187 : Bounds (199042186209 / 1000000000000) (99521093697 / 500000000000) x187 := by
    apply bounds_mul hx184 hx186 <;> norm_num
  let x188 : ℝ := -(183201 / 1000000)
  have hx188 : Bounds (-183201 / 1000000) (-183201 / 1000000) x188 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((183201 / 1000000) : ℝ))
  let x189 : ℝ := (1 / 1)+x188
  have hx189 : Bounds (816799 / 1000000) (816799 / 1000000) x189 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx188 <;> norm_num
  let x190 : ℝ := (1 / 1)-(183201 / 1000000)
  have hx190 : Bounds (816799 / 1000000) (816799 / 1000000) x190 := by
    exact hx189
  let x191 : ℝ := -(183201 / 1000000)
  have hx191 : Bounds (-183201 / 1000000) (-183201 / 1000000) x191 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((183201 / 1000000) : ℝ))
  let x192 : ℝ := (1 / 1)+x191
  have hx192 : Bounds (816799 / 1000000) (816799 / 1000000) x192 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx191 <;> norm_num
  let x193 : ℝ := (1 / 1)-(183201 / 1000000)
  have hx193 : Bounds (816799 / 1000000) (816799 / 1000000) x193 := by
    exact hx192
  let x194 : ℝ := Real.log x193
  have hx194 : Bounds (-202362237 / 1000000000) (-50590559 / 250000000) x194 := by
    exact bounds_log hx193 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x195 : ℝ := x190*x194
  have hx195 : Bounds (-8264463641 / 50000000000) (-82644636001 / 500000000000) x195 := by
    apply bounds_mul hx190 hx194 <;> norm_num
  let x196 : ℝ := x187+x195
  have hx196 : Bounds (33752913389 / 1000000000000) (527389303 / 15625000000) x196 := by
    apply bounds_add hx187 hx195 <;> norm_num
  let x197 : ℝ := (2 / 1)⁻¹
  have hx197 : Bounds (1 / 2) (1 / 2) x197 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x198 : ℝ := x196*x197
  have hx198 : Bounds (8438228347 / 500000000000) (527389303 / 31250000000) x198 := by
    apply bounds_mul hx196 hx197 <;> norm_num
  let x199 : ℝ := x196/(2 / 1)
  have hx199 : Bounds (8438228347 / 500000000000) (527389303 / 31250000000) x199 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx198
  let x200 : ℝ := -x199
  have hx200 : Bounds (-527389303 / 31250000000) (-8438228347 / 500000000000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx199
  let x201 : ℝ := x183+x200
  have hx201 : Bounds (2641682509 / 3906250000) (338135362153 / 500000000000) x201 := by
    apply bounds_add hx183 hx200 <;> norm_num
  let x202 : ℝ := x183-x199
  have hx202 : Bounds (2641682509 / 3906250000) (338135362153 / 500000000000) x202 := by
    exact hx201
  let x203 : ℝ := biasE (183201 / 1000000)
  have hx203 : Bounds (2641682509 / 3906250000) (338135362153 / 500000000000) x203 := by
    simpa +zetaDelta only [biasE, div_one] using hx202
  let x204 : ℝ := Real.log (2 / 1)
  have hx204 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x204 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x205 : ℝ := (1 / 1)+(36577 / 200000)
  have hx205 : Bounds (236577 / 200000) (236577 / 200000) x205 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((36577 / 200000) : ℝ)) <;> norm_num
  let x206 : ℝ := (1 / 1)+(36577 / 200000)
  have hx206 : Bounds (236577 / 200000) (236577 / 200000) x206 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((36577 / 200000) : ℝ)) <;> norm_num
  let x207 : ℝ := Real.log x206
  have hx207 : Bounds (167956369 / 1000000000) (16795637 / 100000000) x207 := by
    exact bounds_log hx206 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x208 : ℝ := x205*x207
  have hx208 : Bounds (24834133693 / 125000000000) (24834133841 / 125000000000) x208 := by
    apply bounds_mul hx205 hx207 <;> norm_num
  let x209 : ℝ := -(36577 / 200000)
  have hx209 : Bounds (-36577 / 200000) (-36577 / 200000) x209 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((36577 / 200000) : ℝ))
  let x210 : ℝ := (1 / 1)+x209
  have hx210 : Bounds (163423 / 200000) (163423 / 200000) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx209 <;> norm_num
  let x211 : ℝ := (1 / 1)-(36577 / 200000)
  have hx211 : Bounds (163423 / 200000) (163423 / 200000) x211 := by
    exact hx210
  let x212 : ℝ := -(36577 / 200000)
  have hx212 : Bounds (-36577 / 200000) (-36577 / 200000) x212 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((36577 / 200000) : ℝ))
  let x213 : ℝ := (1 / 1)+x212
  have hx213 : Bounds (163423 / 200000) (163423 / 200000) x213 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx212 <;> norm_num
  let x214 : ℝ := (1 / 1)-(36577 / 200000)
  have hx214 : Bounds (163423 / 200000) (163423 / 200000) x214 := by
    exact hx213
  let x215 : ℝ := Real.log x214
  have hx215 : Bounds (-50493859 / 250000000) (-40395087 / 200000000) x215 := by
    exact bounds_log hx214 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x216 : ℝ := x211*x215
  have hx216 : Bounds (-41259289597 / 250000000000) (-16503715757 / 100000000000) x216 := by
    apply bounds_mul hx211 hx215 <;> norm_num
  let x217 : ℝ := x208+x216
  have hx217 : Bounds (8408977789 / 250000000000) (16817956579 / 500000000000) x217 := by
    apply bounds_add hx208 hx216 <;> norm_num
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (8408977789 / 500000000000) (16817956579 / 1000000000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (8408977789 / 500000000000) (16817956579 / 1000000000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := -x220
  have hx221 : Bounds (-16817956579 / 1000000000000) (-8408977789 / 500000000000) x221 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx220
  let x222 : ℝ := x204+x221
  have hx222 : Bounds (676329223421 / 1000000000000) (338164612711 / 500000000000) x222 := by
    apply bounds_add hx204 hx221 <;> norm_num
  let x223 : ℝ := x204-x220
  have hx223 : Bounds (676329223421 / 1000000000000) (338164612711 / 500000000000) x223 := by
    exact hx222
  let x224 : ℝ := biasE (36577 / 200000)
  have hx224 : Bounds (676329223421 / 1000000000000) (338164612711 / 500000000000) x224 := by
    simpa +zetaDelta only [biasE, div_one] using hx223
  let x225 : ℝ := biasE c
  have hx225 : Bounds (2641682509 / 3906250000) (338164612711 / 500000000000) x225 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx203.1 hx224.2
  let x226 : ℝ := x159⁻¹
  have hx226 : Bounds (3843886064257 / 1000000000000) (3850579583849 / 1000000000000) x226 := by
    apply bounds_inv hx159 <;> norm_num
  let x227 : ℝ := x148*x226
  have hx227 : Bounds (1436472317 / 1000000000) (720780281139 / 500000000000) x227 := by
    apply bounds_mul hx148 hx226 <;> norm_num
  let x228 : ℝ := x148/x159
  have hx228 : Bounds (1436472317 / 1000000000) (720780281139 / 500000000000) x228 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx227
  let x229 : ℝ := c*x148
  have hx229 : Bounds (68344699947 / 1000000000000) (13717173263 / 200000000000) x229 := by
    apply bounds_mul hc hx148 <;> norm_num
  let x230 : ℝ := x225+x229
  have hx230 : Bounds (744615422251 / 1000000000000) (744915091737 / 1000000000000) x230 := by
    apply bounds_add hx225 hx229 <;> norm_num
  let x231 : ℝ := x*x170
  have hx231 : Bounds (1321494667 / 40000000000) (2071878143 / 62500000000) x231 := by
    apply bounds_mul hx hx170 <;> norm_num
  let x232 : ℝ := x48+x231
  have hx232 : Bounds (693456530381 / 1000000000000) (13873575943 / 20000000000) x232 := by
    apply bounds_add hx48 hx231 <;> norm_num
  let x233 : ℝ := x232⁻¹
  have hx233 : Bounds (22524834353 / 15625000000) (1442051456997 / 1000000000000) x233 := by
    apply bounds_inv hx232 <;> norm_num
  let x234 : ℝ := x230*x233
  have hx234 : Bounds (214685939749 / 200000000000) (1074205893379 / 1000000000000) x234 := by
    apply bounds_mul hx230 hx233 <;> norm_num
  let x235 : ℝ := x230/x232
  have hx235 : Bounds (214685939749 / 200000000000) (1074205893379 / 1000000000000) x235 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx234
  let x236 : ℝ := y*y
  have hx236 : Bounds (15752961 / 244140625) (64739204721 / 1000000000000) x236 := by
    apply bounds_mul hy hy <;> norm_num
  let x237 : ℝ := -x236
  have hx237 : Bounds (-64739204721 / 1000000000000) (-15752961 / 244140625) x237 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx236
  let x238 : ℝ := (1 / 1)+x237
  have hx238 : Bounds (935260795279 / 1000000000000) (228387664 / 244140625) x238 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx237 <;> norm_num
  let x239 : ℝ := (1 / 1)-x236
  have hx239 : Bounds (935260795279 / 1000000000000) (228387664 / 244140625) x239 := by
    exact hx238
  let x240 : ℝ := x239*x159
  have hx240 : Bounds (242888317177 / 1000000000000) (243367221637 / 1000000000000) x240 := by
    apply bounds_mul hx239 hx159 <;> norm_num
  let x241 : ℝ := c*c
  have hx241 : Bounds (1337876929 / 40000000000) (33562606401 / 1000000000000) x241 := by
    apply bounds_mul hc hc <;> norm_num
  let x242 : ℝ := -x241
  have hx242 : Bounds (-33562606401 / 1000000000000) (-1337876929 / 40000000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx241
  let x243 : ℝ := (1 / 1)+x242
  have hx243 : Bounds (966437393599 / 1000000000000) (38662123071 / 40000000000) x243 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx242 <;> norm_num
  let x244 : ℝ := (1 / 1)-x241
  have hx244 : Bounds (966437393599 / 1000000000000) (38662123071 / 40000000000) x244 := by
    exact hx243
  let x245 : ℝ := x244*x182
  have hx245 : Bounds (27452880091 / 40000000000) (10725968777 / 15625000000) x245 := by
    apply bounds_mul hx244 hx182 <;> norm_num
  let x246 : ℝ := y*y
  have hx246 : Bounds (15752961 / 244140625) (64739204721 / 1000000000000) x246 := by
    apply bounds_mul hy hy <;> norm_num
  let x247 : ℝ := (1 / 1)+x246
  have hx247 : Bounds (259893586 / 244140625) (1064739204721 / 1000000000000) x247 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx246 <;> norm_num
  let x248 : ℝ := x247*x159
  have hx248 : Bounds (138229077607 / 500000000000) (69248879059 / 250000000000) x248 := by
    apply bounds_mul hx247 hx159 <;> norm_num
  let x249 : ℝ := -y
  have hx249 : Bounds (-254439 / 1000000) (-3969 / 15625) x249 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x250 : ℝ := x248+x249
  have hx250 : Bounds (11009577607 / 500000000000) (5744879059 / 250000000000) x250 := by
    apply bounds_add hx248 hx249 <;> norm_num
  let x251 : ℝ := x248-y
  have hx251 : Bounds (11009577607 / 500000000000) (5744879059 / 250000000000) x251 := by
    exact hx250
  let x252 : ℝ := x240*x240
  have hx252 : Bounds (58994734621 / 1000000000000) (7403450571 / 125000000000) x252 := by
    apply bounds_mul hx240 hx240 <;> norm_num
  let x253 : ℝ := x252⁻¹
  have hx253 : Bounds (8442009492819 / 500000000000) (8475332641331 / 500000000000) x253 := by
    apply bounds_inv hx252 <;> norm_num
  let x254 : ℝ := x251*x253
  have hx254 : Bounds (9294295867 / 25000000000) (194759044037 / 500000000000) x254 := by
    apply bounds_mul hx251 hx253 <;> norm_num
  let x255 : ℝ := x251/x252
  have hx255 : Bounds (9294295867 / 25000000000) (194759044037 / 500000000000) x255 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx254
  let x256 : ℝ := (-2 / 1)*x255
  have hx256 : Bounds (-194759044037 / 250000000000) (-9294295867 / 12500000000) x256 := by
    apply bounds_mul (bounds_const ((-2 / 1) : ℝ)) hx255 <;> norm_num
  let x257 : ℝ := x256*x228
  have hx257 : Bounds (-1123027828123 / 1000000000000) (-267019974379 / 250000000000) x257 := by
    apply bounds_mul hx256 hx228 <;> norm_num
  let x258 : ℝ := (2 / 1)*x182
  have hx258 : Bounds (56812537 / 40000000) (1420433121 / 1000000000) x258 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx182 <;> norm_num
  let x259 : ℝ := c*c
  have hx259 : Bounds (1337876929 / 40000000000) (33562606401 / 1000000000000) x259 := by
    apply bounds_mul hc hc <;> norm_num
  let x260 : ℝ := -x259
  have hx260 : Bounds (-33562606401 / 1000000000000) (-1337876929 / 40000000000) x260 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx259
  let x261 : ℝ := x258+x260
  have hx261 : Bounds (1386750818599 / 1000000000000) (55479447911 / 40000000000) x261 := by
    apply bounds_add hx258 hx260 <;> norm_num
  let x262 : ℝ := x258-x259
  have hx262 : Bounds (1386750818599 / 1000000000000) (55479447911 / 40000000000) x262 := by
    exact hx261
  let x263 : ℝ := c*x262
  have hx263 : Bounds (253615923459 / 1000000000000) (254097258419 / 1000000000000) x263 := by
    apply bounds_mul hc hx262 <;> norm_num
  let x264 : ℝ := x245*x245
  have hx264 : Bounds (235518945403 / 500000000000) (471230079817 / 1000000000000) x264 := by
    apply bounds_mul hx245 hx245 <;> norm_num
  let x265 : ℝ := x264⁻¹
  have hx265 : Bounds (212210561853 / 100000000000) (1061485731317 / 500000000000) x265 := by
    apply bounds_inv hx264 <;> norm_num
  let x266 : ℝ := x263*x265
  have hx266 : Bounds (538199776121 / 1000000000000) (269720614179 / 500000000000) x266 := by
    apply bounds_mul hx263 hx265 <;> norm_num
  let x267 : ℝ := x263/x264
  have hx267 : Bounds (538199776121 / 1000000000000) (269720614179 / 500000000000) x267 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx266
  let x268 : ℝ := (2 / 1)*x267
  have hx268 : Bounds (538199776121 / 500000000000) (269720614179 / 250000000000) x268 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx267 <;> norm_num
  let x269 : ℝ := x268*x235
  have hx269 : Bounds (288859811773 / 250000000000) (289735473317 / 250000000000) x269 := by
    apply bounds_mul hx268 hx235 <;> norm_num
  let x270 : ℝ := x257+x269
  have hx270 : Bounds (32411418969 / 1000000000000) (11357749469 / 125000000000) x270 := by
    apply bounds_add hx257 hx269 <;> norm_num
  have hPos : 0 < x270 :=
    lt_of_lt_of_le (by norm_num) hx270.1
  have hBridgeL : doubleCapBridgeL x = x48 := by
    exact hEll'
  rw [← doubleCapBridgeDerivativeTraceForm_eq x]
  simpa +zetaDelta only [doubleCapBridgeDerivativeTraceForm,
    hBridgeL, SmallMean.A, biasB, div_one, pow_two] using hPos

theorem acceptedCell : DoubleCapBridgeDerivativeCellCertificate
    (⟨183, by decide⟩ : Fin 256) doubleCapBridgeDerivativeExpression where
  positive x hx := by
    have hloEq : doubleCapBridgeLo (⟨183, by decide⟩ : Fin 256) =
        (1829 / 10240) := by norm_num [doubleCapBridgeLo, doubleCapBridgeStep]
    have hhiEq : doubleCapBridgeHi (⟨183, by decide⟩ : Fin 256) =
        (229 / 1280) := by norm_num [doubleCapBridgeHi, doubleCapBridgeStep]
    have hlo : (1829 / 10240) ≤ x := by
      simpa only [hloEq] using hx.1
    have hhi : x ≤ (229 / 1280) := by
      simpa only [hhiEq] using hx.2
    exact cell_derivative_pos x ⟨hlo, hhi⟩

#print axioms cell_derivative_pos
#print axioms acceptedCell

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell183

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell184 =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell184
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_derivative_pos (x : ℝ)
    (hx : Bounds (229 / 1280) (367 / 2048) x) :
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
  have hx0 : Bounds (229 / 640) (367 / 1024) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx <;> norm_num
  let x1 : ℝ := Real.log (2 / 1)
  have hx1 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x1 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x2 : ℝ := Real.log (2 / 1)
  have hx2 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x2 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x3 : ℝ := (1 / 1)+(367 / 1024)
  have hx3 : Bounds (1391 / 1024) (1391 / 1024) x3 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((367 / 1024) : ℝ)) <;> norm_num
  let x4 : ℝ := (1 / 1)+(367 / 1024)
  have hx4 : Bounds (1391 / 1024) (1391 / 1024) x4 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((367 / 1024) : ℝ)) <;> norm_num
  let x5 : ℝ := Real.log x4
  have hx5 : Bounds (153153193 / 500000000) (306306387 / 1000000000) x5 := by
    exact bounds_log hx4 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x6 : ℝ := x3*x5
  have hx6 : Bounds (208043058069 / 500000000000) (208043058749 / 500000000000) x6 := by
    apply bounds_mul hx3 hx5 <;> norm_num
  let x7 : ℝ := -(367 / 1024)
  have hx7 : Bounds (-367 / 1024) (-367 / 1024) x7 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((367 / 1024) : ℝ))
  let x8 : ℝ := (1 / 1)+x7
  have hx8 : Bounds (657 / 1024) (657 / 1024) x8 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx7 <;> norm_num
  let x9 : ℝ := (1 / 1)-(367 / 1024)
  have hx9 : Bounds (657 / 1024) (657 / 1024) x9 := by
    exact hx8
  let x10 : ℝ := -(367 / 1024)
  have hx10 : Bounds (-367 / 1024) (-367 / 1024) x10 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((367 / 1024) : ℝ))
  let x11 : ℝ := (1 / 1)+x10
  have hx11 : Bounds (657 / 1024) (657 / 1024) x11 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx10 <;> norm_num
  let x12 : ℝ := (1 / 1)-(367 / 1024)
  have hx12 : Bounds (657 / 1024) (657 / 1024) x12 := by
    exact hx11
  let x13 : ℝ := Real.log x12
  have hx13 : Bounds (-110946947 / 250000000) (-443787787 / 1000000000) x13 := by
    exact bounds_log hx12 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x14 : ℝ := x9*x13
  have hx14 : Bounds (-1423674691 / 5000000000) (-284734937557 / 1000000000000) x14 := by
    apply bounds_mul hx9 hx13 <;> norm_num
  let x15 : ℝ := x6+x14
  have hx15 : Bounds (65675588969 / 500000000000) (131351179941 / 1000000000000) x15 := by
    apply bounds_add hx6 hx14 <;> norm_num
  let x16 : ℝ := (2 / 1)⁻¹
  have hx16 : Bounds (1 / 2) (1 / 2) x16 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x17 : ℝ := x15*x16
  have hx17 : Bounds (65675588969 / 1000000000000) (65675589971 / 1000000000000) x17 := by
    apply bounds_mul hx15 hx16 <;> norm_num
  let x18 : ℝ := x15/(2 / 1)
  have hx18 : Bounds (65675588969 / 1000000000000) (65675589971 / 1000000000000) x18 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx17
  let x19 : ℝ := -x18
  have hx19 : Bounds (-65675589971 / 1000000000000) (-65675588969 / 1000000000000) x19 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx18
  let x20 : ℝ := x2+x19
  have hx20 : Bounds (627471590029 / 1000000000000) (627471592031 / 1000000000000) x20 := by
    apply bounds_add hx2 hx19 <;> norm_num
  let x21 : ℝ := x2-x18
  have hx21 : Bounds (627471590029 / 1000000000000) (627471592031 / 1000000000000) x21 := by
    exact hx20
  let x22 : ℝ := biasE (367 / 1024)
  have hx22 : Bounds (627471590029 / 1000000000000) (627471592031 / 1000000000000) x22 := by
    simpa +zetaDelta only [biasE, div_one] using hx21
  let x23 : ℝ := Real.log (2 / 1)
  have hx23 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x23 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x24 : ℝ := (1 / 1)+(229 / 640)
  have hx24 : Bounds (869 / 640) (869 / 640) x24 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((229 / 640) : ℝ)) <;> norm_num
  let x25 : ℝ := (1 / 1)+(229 / 640)
  have hx25 : Bounds (869 / 640) (869 / 640) x25 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((229 / 640) : ℝ)) <;> norm_num
  let x26 : ℝ := Real.log x25
  have hx26 : Bounds (76468737 / 250000000) (305874949 / 1000000000) x26 := by
    exact bounds_log hx25 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x27 : ℝ := x24*x26
  have hx27 : Bounds (415320827831 / 1000000000000) (41532082919 / 100000000000) x27 := by
    apply bounds_mul hx24 hx26 <;> norm_num
  let x28 : ℝ := -(229 / 640)
  have hx28 : Bounds (-229 / 640) (-229 / 640) x28 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((229 / 640) : ℝ))
  let x29 : ℝ := (1 / 1)+x28
  have hx29 : Bounds (411 / 640) (411 / 640) x29 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx28 <;> norm_num
  let x30 : ℝ := (1 / 1)-(229 / 640)
  have hx30 : Bounds (411 / 640) (411 / 640) x30 := by
    exact hx29
  let x31 : ℝ := -(229 / 640)
  have hx31 : Bounds (-229 / 640) (-229 / 640) x31 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((229 / 640) : ℝ))
  let x32 : ℝ := (1 / 1)+x31
  have hx32 : Bounds (411 / 640) (411 / 640) x32 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx31 <;> norm_num
  let x33 : ℝ := (1 / 1)-(229 / 640)
  have hx33 : Bounds (411 / 640) (411 / 640) x33 := by
    exact hx32
  let x34 : ℝ := Real.log x33
  have hx34 : Bounds (-221437481 / 500000000) (-442874961 / 1000000000) x34 := by
    exact bounds_log hx33 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x35 : ℝ := x30*x34
  have hx35 : Bounds (-14220438233 / 50000000000) (-284408764017 / 1000000000000) x35 := by
    apply bounds_mul hx30 hx34 <;> norm_num
  let x36 : ℝ := x27+x35
  have hx36 : Bounds (130912063171 / 1000000000000) (130912065173 / 1000000000000) x36 := by
    apply bounds_add hx27 hx35 <;> norm_num
  let x37 : ℝ := (2 / 1)⁻¹
  have hx37 : Bounds (1 / 2) (1 / 2) x37 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x38 : ℝ := x36*x37
  have hx38 : Bounds (13091206317 / 200000000000) (65456032587 / 1000000000000) x38 := by
    apply bounds_mul hx36 hx37 <;> norm_num
  let x39 : ℝ := x36/(2 / 1)
  have hx39 : Bounds (13091206317 / 200000000000) (65456032587 / 1000000000000) x39 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx38
  let x40 : ℝ := -x39
  have hx40 : Bounds (-65456032587 / 1000000000000) (-13091206317 / 200000000000) x40 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx39
  let x41 : ℝ := x23+x40
  have hx41 : Bounds (627691147413 / 1000000000000) (125538229883 / 200000000000) x41 := by
    apply bounds_add hx23 hx40 <;> norm_num
  let x42 : ℝ := x23-x39
  have hx42 : Bounds (627691147413 / 1000000000000) (125538229883 / 200000000000) x42 := by
    exact hx41
  let x43 : ℝ := biasE (229 / 640)
  have hx43 : Bounds (627691147413 / 1000000000000) (125538229883 / 200000000000) x43 := by
    simpa +zetaDelta only [biasE, div_one] using hx42
  let x44 : ℝ := biasE x0
  have hx44 : Bounds (627471590029 / 1000000000000) (125538229883 / 200000000000) x44 := by
    exact bounds_biasE hx0 (by norm_num) (by norm_num) hx22.1 hx43.2
  let x45 : ℝ := x1+x44
  have hx45 : Bounds (1320618770029 / 1000000000000) (264167666083 / 200000000000) x45 := by
    apply bounds_add hx1 hx44 <;> norm_num
  let x46 : ℝ := (2 / 1)⁻¹
  have hx46 : Bounds (1 / 2) (1 / 2) x46 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x47 : ℝ := x45*x46
  have hx47 : Bounds (330154692507 / 500000000000) (82552395651 / 125000000000) x47 := by
    apply bounds_mul hx45 hx46 <;> norm_num
  let x48 : ℝ := x45/(2 / 1)
  have hx48 : Bounds (330154692507 / 500000000000) (82552395651 / 125000000000) x48 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx47
  let x49 : ℝ := Real.log (2 / 1)
  have hx49 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x49 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x50 : ℝ := (1 / 1)+(127219 / 500000)
  have hx50 : Bounds (627219 / 500000) (627219 / 500000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((127219 / 500000) : ℝ)) <;> norm_num
  let x51 : ℝ := (1 / 1)+(127219 / 500000)
  have hx51 : Bounds (627219 / 500000) (627219 / 500000) x51 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((127219 / 500000) : ℝ)) <;> norm_num
  let x52 : ℝ := Real.log x51
  have hx52 : Bounds (226687663 / 1000000000) (14167979 / 62500000) x52 := by
    exact bounds_log hx51 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x53 : ℝ := x50*x52
  have hx53 : Bounds (142182809299 / 500000000000) (284365619853 / 1000000000000) x53 := by
    apply bounds_mul hx50 hx52 <;> norm_num
  let x54 : ℝ := -(127219 / 500000)
  have hx54 : Bounds (-127219 / 500000) (-127219 / 500000) x54 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((127219 / 500000) : ℝ))
  let x55 : ℝ := (1 / 1)+x54
  have hx55 : Bounds (372781 / 500000) (372781 / 500000) x55 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx54 <;> norm_num
  let x56 : ℝ := (1 / 1)-(127219 / 500000)
  have hx56 : Bounds (372781 / 500000) (372781 / 500000) x56 := by
    exact hx55
  let x57 : ℝ := -(127219 / 500000)
  have hx57 : Bounds (-127219 / 500000) (-127219 / 500000) x57 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((127219 / 500000) : ℝ))
  let x58 : ℝ := (1 / 1)+x57
  have hx58 : Bounds (372781 / 500000) (372781 / 500000) x58 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx57 <;> norm_num
  let x59 : ℝ := (1 / 1)-(127219 / 500000)
  have hx59 : Bounds (372781 / 500000) (372781 / 500000) x59 := by
    exact hx58
  let x60 : ℝ := Real.log x59
  have hx60 : Bounds (-293616983 / 1000000000) (-146808491 / 500000000) x60 := by
    exact bounds_log hx59 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x61 : ℝ := x56*x60
  have hx61 : Bounds (-5472741627 / 25000000000) (-218909664333 / 1000000000000) x61 := by
    apply bounds_mul hx56 hx60 <;> norm_num
  let x62 : ℝ := x53+x61
  have hx62 : Bounds (32727976759 / 500000000000) (204549861 / 3125000000) x62 := by
    apply bounds_add hx53 hx61 <;> norm_num
  let x63 : ℝ := (2 / 1)⁻¹
  have hx63 : Bounds (1 / 2) (1 / 2) x63 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x64 : ℝ := x62*x63
  have hx64 : Bounds (32727976759 / 1000000000000) (204549861 / 6250000000) x64 := by
    apply bounds_mul hx62 hx63 <;> norm_num
  let x65 : ℝ := x62/(2 / 1)
  have hx65 : Bounds (32727976759 / 1000000000000) (204549861 / 6250000000) x65 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx64
  let x66 : ℝ := -x65
  have hx66 : Bounds (-204549861 / 6250000000) (-32727976759 / 1000000000000) x66 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx65
  let x67 : ℝ := x49+x66
  have hx67 : Bounds (2063810007 / 3125000000) (660419204241 / 1000000000000) x67 := by
    apply bounds_add hx49 hx66 <;> norm_num
  let x68 : ℝ := x49-x65
  have hx68 : Bounds (2063810007 / 3125000000) (660419204241 / 1000000000000) x68 := by
    exact hx67
  let x69 : ℝ := biasE (127219 / 500000)
  have hx69 : Bounds (2063810007 / 3125000000) (660419204241 / 1000000000000) x69 := by
    simpa +zetaDelta only [biasE, div_one] using hx68
  let x70 : ℝ := Real.log (2 / 1)
  have hx70 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x70 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x71 : ℝ := (1 / 1)+(12743 / 50000)
  have hx71 : Bounds (62743 / 50000) (62743 / 50000) x71 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((12743 / 50000) : ℝ)) <;> norm_num
  let x72 : ℝ := (1 / 1)+(12743 / 50000)
  have hx72 : Bounds (62743 / 50000) (62743 / 50000) x72 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((12743 / 50000) : ℝ)) <;> norm_num
  let x73 : ℝ := Real.log x72
  have hx73 : Bounds (56756003 / 250000000) (227024013 / 1000000000) x73 := by
    exact bounds_log hx72 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x74 : ℝ := x71*x73
  have hx74 : Bounds (142441675849 / 500000000000) (142441676477 / 500000000000) x74 := by
    apply bounds_mul hx71 hx73 <;> norm_num
  let x75 : ℝ := -(12743 / 50000)
  have hx75 : Bounds (-12743 / 50000) (-12743 / 50000) x75 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((12743 / 50000) : ℝ))
  let x76 : ℝ := (1 / 1)+x75
  have hx76 : Bounds (37257 / 50000) (37257 / 50000) x76 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx75 <;> norm_num
  let x77 : ℝ := (1 / 1)-(12743 / 50000)
  have hx77 : Bounds (37257 / 50000) (37257 / 50000) x77 := by
    exact hx76
  let x78 : ℝ := -(12743 / 50000)
  have hx78 : Bounds (-12743 / 50000) (-12743 / 50000) x78 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((12743 / 50000) : ℝ))
  let x79 : ℝ := (1 / 1)+x78
  have hx79 : Bounds (37257 / 50000) (37257 / 50000) x79 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx78 <;> norm_num
  let x80 : ℝ := (1 / 1)-(12743 / 50000)
  have hx80 : Bounds (37257 / 50000) (37257 / 50000) x80 := by
    exact hx79
  let x81 : ℝ := Real.log x80
  have hx81 : Bounds (-294183159 / 1000000000) (-147091579 / 500000000) x81 := by
    exact bounds_log hx80 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x82 : ℝ := x77*x81
  have hx82 : Bounds (-109603819549 / 500000000000) (-13700477397 / 62500000000) x82 := by
    apply bounds_mul hx77 hx81 <;> norm_num
  let x83 : ℝ := x74+x82
  have hx83 : Bounds (328378563 / 5000000000) (32837857301 / 500000000000) x83 := by
    apply bounds_add hx74 hx82 <;> norm_num
  let x84 : ℝ := (2 / 1)⁻¹
  have hx84 : Bounds (1 / 2) (1 / 2) x84 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x85 : ℝ := x83*x84
  have hx85 : Bounds (328378563 / 10000000000) (32837857301 / 1000000000000) x85 := by
    apply bounds_mul hx83 hx84 <;> norm_num
  let x86 : ℝ := x83/(2 / 1)
  have hx86 : Bounds (328378563 / 10000000000) (32837857301 / 1000000000000) x86 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx85
  let x87 : ℝ := -x86
  have hx87 : Bounds (-32837857301 / 1000000000000) (-328378563 / 10000000000) x87 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx86
  let x88 : ℝ := x70+x87
  have hx88 : Bounds (660309322699 / 1000000000000) (6603093247 / 10000000000) x88 := by
    apply bounds_add hx70 hx87 <;> norm_num
  let x89 : ℝ := x70-x86
  have hx89 : Bounds (660309322699 / 1000000000000) (6603093247 / 10000000000) x89 := by
    exact hx88
  let x90 : ℝ := biasE (12743 / 50000)
  have hx90 : Bounds (660309322699 / 1000000000000) (6603093247 / 10000000000) x90 := by
    simpa +zetaDelta only [biasE, div_one] using hx89
  let y : ℝ := doubleCapHighTailY x
  have hEll' : Real.log 2 * doubleCapHighTailFloor x = x48 := by
    simpa +zetaDelta only [div_one] using hEll
  have hy : Bounds (127219 / 500000) (12743 / 50000) y := by
    dsimp only [y, doubleCapHighTailY]
    apply entropyInverseBias_bracket hh0.le hh1.le
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (12743 / 50000) ≤ (6603093247 / 10000000000) := hx90.2
      have h2 : (330154692507 / 500000000000) ≤ x48 := hx48.1
      linarith [hEll']
    · have h1 : x48 ≤ (82552395651 / 125000000000) := hx48.2
      have h2 : (2063810007 / 3125000000) ≤ biasE (127219 / 500000) := hx69.1
      linarith [hEll']
  let x91 : ℝ := x⁻¹
  have hx91 : Bounds (5580381471389 / 1000000000000) (174672489083 / 31250000000) x91 := by
    apply bounds_inv hx <;> norm_num
  let x92 : ℝ := x48*x91
  have hx92 : Bounds (921194564379 / 250000000000) (4614282377 / 1250000000) x92 := by
    apply bounds_mul hx48 hx91 <;> norm_num
  let x93 : ℝ := x48/x
  have hx93 : Bounds (921194564379 / 250000000000) (4614282377 / 1250000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(229 / 1250)
  have hx95 : Bounds (1479 / 1250) (1479 / 1250) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((229 / 1250) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(229 / 1250)
  have hx96 : Bounds (1479 / 1250) (1479 / 1250) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((229 / 1250) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (21027829 / 125000000) (168222633 / 1000000000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (99520509091 / 500000000000) (99520509683 / 500000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(229 / 1250)
  have hx99 : Bounds (-229 / 1250) (-229 / 1250) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((229 / 1250) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (1021 / 1250) (1021 / 1250) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(229 / 1250)
  have hx101 : Bounds (1021 / 1250) (1021 / 1250) x101 := by
    exact hx100
  let x102 : ℝ := -(229 / 1250)
  have hx102 : Bounds (-229 / 1250) (-229 / 1250) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((229 / 1250) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (1021 / 1250) (1021 / 1250) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(229 / 1250)
  have hx104 : Bounds (1021 / 1250) (1021 / 1250) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-202361013 / 1000000000) (-50590253 / 250000000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-165288475419 / 1000000000000) (-165288474601 / 1000000000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (33752542763 / 1000000000000) (6750508953 / 200000000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (16876271381 / 1000000000000) (16876272383 / 1000000000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (16876271381 / 1000000000000) (16876272383 / 1000000000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-16876272383 / 1000000000000) (-16876271381 / 1000000000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (676270907617 / 1000000000000) (676270909619 / 1000000000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (676270907617 / 1000000000000) (676270909619 / 1000000000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (229 / 1250)
  have hx114 : Bounds (676270907617 / 1000000000000) (676270909619 / 1000000000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(45879 / 250000)
  have hx116 : Bounds (295879 / 250000) (295879 / 250000) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((45879 / 250000) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(45879 / 250000)
  have hx117 : Bounds (295879 / 250000) (295879 / 250000) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((45879 / 250000) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (168489669 / 1000000000) (16848967 / 100000000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (24926277387 / 125000000000) (4985255507 / 25000000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(45879 / 250000)
  have hx120 : Bounds (-45879 / 250000) (-45879 / 250000) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((45879 / 250000) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (204121 / 250000) (204121 / 250000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(45879 / 250000)
  have hx122 : Bounds (204121 / 250000) (204121 / 250000) x122 := by
    exact hx121
  let x123 : ℝ := -(45879 / 250000)
  have hx123 : Bounds (-45879 / 250000) (-45879 / 250000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((45879 / 250000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (204121 / 250000) (204121 / 250000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(45879 / 250000)
  have hx125 : Bounds (204121 / 250000) (204121 / 250000) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-202747963 / 1000000000) (-101373981 / 500000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-165540467823 / 1000000000000) (-33108093401 / 200000000000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (33869751273 / 1000000000000) (1354790131 / 40000000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (4233718909 / 250000000000) (8467438319 / 500000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (4233718909 / 250000000000) (8467438319 / 500000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-8467438319 / 500000000000) (-4233718909 / 250000000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (338106151681 / 500000000000) (169053076341 / 250000000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (338106151681 / 500000000000) (169053076341 / 250000000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (45879 / 250000)
  have hx135 : Bounds (338106151681 / 500000000000) (169053076341 / 250000000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(229 / 1250)
  have hx136 : Bounds (84381422097 / 125000000000) (338134612587 / 500000000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((229 / 1250) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(45879 / 250000)
  have hx137 : Bounds (338107883353 / 500000000000) (677435715759 / 1000000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((45879 / 250000) : ℝ)) <;> norm_num
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
  have hc : Bounds (229 / 1250) (45879 / 250000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num)
      (by norm_num) (show 0 < x93 by linarith [hx93.1]) hcEq
    · have h1 : x93 * (229 / 1250) ≤ (338134612587 / 500000000000) := hx136.2
      have h2 : (676270907617 / 1000000000000) ≤ biasE (229 / 1250) := hx114.1
      linarith
    · have h1 : biasE (45879 / 250000) ≤ (169053076341 / 250000000000) := hx135.2
      have h2 : (338107883353 / 500000000000) ≤ x93 * (45879 / 250000) := hx137.1
      linarith
  let x138 : ℝ := (1 / 1)+x0
  have hx138 : Bounds (869 / 640) (1391 / 1024) x138 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx0 <;> norm_num
  let x139 : ℝ := -x0
  have hx139 : Bounds (-367 / 1024) (-229 / 640) x139 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x140 : ℝ := (1 / 1)+x139
  have hx140 : Bounds (657 / 1024) (411 / 640) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx139 <;> norm_num
  let x141 : ℝ := (1 / 1)-x0
  have hx141 : Bounds (657 / 1024) (411 / 640) x141 := by
    exact hx140
  let x142 : ℝ := x141⁻¹
  have hx142 : Bounds (1557177615571 / 1000000000000) (779299847793 / 500000000000) x142 := by
    apply bounds_inv hx141 <;> norm_num
  let x143 : ℝ := x138*x142
  have hx143 : Bounds (1057177615571 / 500000000000) (529299847793 / 250000000000) x143 := by
    apply bounds_mul hx138 hx142 <;> norm_num
  let x144 : ℝ := x138/x141
  have hx144 : Bounds (1057177615571 / 500000000000) (529299847793 / 250000000000) x144 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx143
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (74874991 / 100000000) (375047087 / 500000000) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_14.2)
  let x146 : ℝ := (2 / 1)⁻¹
  have hx146 : Bounds (1 / 2) (1 / 2) x146 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x147 : ℝ := x145*x146
  have hx147 : Bounds (74874991 / 200000000) (375047087 / 1000000000) x147 := by
    apply bounds_mul hx145 hx146 <;> norm_num
  let x148 : ℝ := x145/(2 / 1)
  have hx148 : Bounds (74874991 / 200000000) (375047087 / 1000000000) x148 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx147
  let x149 : ℝ := (1 / 1)+y
  have hx149 : Bounds (627219 / 500000) (62743 / 50000) x149 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x150 : ℝ := -y
  have hx150 : Bounds (-12743 / 50000) (-127219 / 500000) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (37257 / 50000) (372781 / 500000) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-y
  have hx152 : Bounds (37257 / 50000) (372781 / 500000) x152 := by
    exact hx151
  let x153 : ℝ := x152⁻¹
  have hx153 : Bounds (1341270075459 / 1000000000000) (1342029685697 / 1000000000000) x153 := by
    apply bounds_inv hx152 <;> norm_num
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (841270075459 / 500000000000) (842029685697 / 500000000000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x149/x152
  have hx155 : Bounds (841270075459 / 500000000000) (842029685697 / 500000000000) x155 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx154
  let x156 : ℝ := Real.log x155
  have hx156 : Bounds (260152323 / 500000000) (130301793 / 250000000) x156 := by
    exact bounds_log hx155 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_16.2)
  let x157 : ℝ := (2 / 1)⁻¹
  have hx157 : Bounds (1 / 2) (1 / 2) x157 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x158 : ℝ := x156*x157
  have hx158 : Bounds (260152323 / 1000000000) (130301793 / 500000000) x158 := by
    apply bounds_mul hx156 hx157 <;> norm_num
  let x159 : ℝ := x156/(2 / 1)
  have hx159 : Bounds (260152323 / 1000000000) (130301793 / 500000000) x159 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx158
  let x160 : ℝ := (1 / 1)+c
  have hx160 : Bounds (1479 / 1250) (295879 / 250000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x161 : ℝ := -c
  have hx161 : Bounds (-45879 / 250000) (-229 / 1250) x161 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x162 : ℝ := (1 / 1)+x161
  have hx162 : Bounds (204121 / 250000) (1021 / 1250) x162 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx161 <;> norm_num
  let x163 : ℝ := (1 / 1)-c
  have hx163 : Bounds (204121 / 250000) (1021 / 1250) x163 := by
    exact hx162
  let x164 : ℝ := x163⁻¹
  have hx164 : Bounds (1224289911851 / 1000000000000) (612381871537 / 500000000000) x164 := by
    apply bounds_inv hx163 <;> norm_num
  let x165 : ℝ := x160*x164
  have hx165 : Bounds (724289911851 / 500000000000) (362381871537 / 250000000000) x165 := by
    apply bounds_mul hx160 hx164 <;> norm_num
  let x166 : ℝ := x160/x163
  have hx166 : Bounds (724289911851 / 500000000000) (362381871537 / 250000000000) x166 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx165
  let x167 : ℝ := Real.log x166
  have hx167 : Bounds (92645911 / 250000000) (1450147 / 3906250) x167 := by
    exact bounds_log hx166 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x168 : ℝ := (2 / 1)⁻¹
  have hx168 : Bounds (1 / 2) (1 / 2) x168 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x169 : ℝ := x167*x168
  have hx169 : Bounds (92645911 / 500000000) (1450147 / 7812500) x169 := by
    apply bounds_mul hx167 hx168 <;> norm_num
  let x170 : ℝ := x167/(2 / 1)
  have hx170 : Bounds (92645911 / 500000000) (1450147 / 7812500) x170 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx169
  let x171 : ℝ := Real.log (2 / 1)
  have hx171 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x171 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x172 : ℝ := c*c
  have hx172 : Bounds (52441 / 1562500) (2104882641 / 62500000000) x172 := by
    apply bounds_mul hc hc <;> norm_num
  let x173 : ℝ := -x172
  have hx173 : Bounds (-2104882641 / 62500000000) (-52441 / 1562500) x173 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx172
  let x174 : ℝ := (1 / 1)+x173
  have hx174 : Bounds (60395117359 / 62500000000) (1510059 / 1562500) x174 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx173 <;> norm_num
  let x175 : ℝ := (1 / 1)-x172
  have hx175 : Bounds (60395117359 / 62500000000) (1510059 / 1562500) x175 := by
    exact hx174
  let x176 : ℝ := Real.log x175
  have hx176 : Bounds (-17129147 / 500000000) (-34138379 / 1000000000) x176 := by
    exact bounds_log hx175 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (-17129147 / 1000000000) (-34138379 / 2000000000) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (-17129147 / 1000000000) (-34138379 / 2000000000) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (34138379 / 2000000000) (17129147 / 1000000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x171+x180
  have hx181 : Bounds (1420432739 / 2000000000) (88784541 / 125000000) x181 := by
    apply bounds_add hx171 hx180 <;> norm_num
  let x182 : ℝ := x171-x179
  have hx182 : Bounds (1420432739 / 2000000000) (88784541 / 125000000) x182 := by
    exact hx181
  let x183 : ℝ := Real.log (2 / 1)
  have hx183 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x183 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x184 : ℝ := (1 / 1)+(45879 / 250000)
  have hx184 : Bounds (295879 / 250000) (295879 / 250000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((45879 / 250000) : ℝ)) <;> norm_num
  let x185 : ℝ := (1 / 1)+(45879 / 250000)
  have hx185 : Bounds (295879 / 250000) (295879 / 250000) x185 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((45879 / 250000) : ℝ)) <;> norm_num
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (168489669 / 1000000000) (16848967 / 100000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x187 : ℝ := x184*x186
  have hx187 : Bounds (24926277387 / 125000000000) (4985255507 / 25000000000) x187 := by
    apply bounds_mul hx184 hx186 <;> norm_num
  let x188 : ℝ := -(45879 / 250000)
  have hx188 : Bounds (-45879 / 250000) (-45879 / 250000) x188 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((45879 / 250000) : ℝ))
  let x189 : ℝ := (1 / 1)+x188
  have hx189 : Bounds (204121 / 250000) (204121 / 250000) x189 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx188 <;> norm_num
  let x190 : ℝ := (1 / 1)-(45879 / 250000)
  have hx190 : Bounds (204121 / 250000) (204121 / 250000) x190 := by
    exact hx189
  let x191 : ℝ := -(45879 / 250000)
  have hx191 : Bounds (-45879 / 250000) (-45879 / 250000) x191 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((45879 / 250000) : ℝ))
  let x192 : ℝ := (1 / 1)+x191
  have hx192 : Bounds (204121 / 250000) (204121 / 250000) x192 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx191 <;> norm_num
  let x193 : ℝ := (1 / 1)-(45879 / 250000)
  have hx193 : Bounds (204121 / 250000) (204121 / 250000) x193 := by
    exact hx192
  let x194 : ℝ := Real.log x193
  have hx194 : Bounds (-202747963 / 1000000000) (-101373981 / 500000000) x194 := by
    exact bounds_log hx193 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x195 : ℝ := x190*x194
  have hx195 : Bounds (-165540467823 / 1000000000000) (-33108093401 / 200000000000) x195 := by
    apply bounds_mul hx190 hx194 <;> norm_num
  let x196 : ℝ := x187+x195
  have hx196 : Bounds (33869751273 / 1000000000000) (1354790131 / 40000000000) x196 := by
    apply bounds_add hx187 hx195 <;> norm_num
  let x197 : ℝ := (2 / 1)⁻¹
  have hx197 : Bounds (1 / 2) (1 / 2) x197 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x198 : ℝ := x196*x197
  have hx198 : Bounds (4233718909 / 250000000000) (8467438319 / 500000000000) x198 := by
    apply bounds_mul hx196 hx197 <;> norm_num
  let x199 : ℝ := x196/(2 / 1)
  have hx199 : Bounds (4233718909 / 250000000000) (8467438319 / 500000000000) x199 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx198
  let x200 : ℝ := -x199
  have hx200 : Bounds (-8467438319 / 500000000000) (-4233718909 / 250000000000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx199
  let x201 : ℝ := x183+x200
  have hx201 : Bounds (338106151681 / 500000000000) (169053076341 / 250000000000) x201 := by
    apply bounds_add hx183 hx200 <;> norm_num
  let x202 : ℝ := x183-x199
  have hx202 : Bounds (338106151681 / 500000000000) (169053076341 / 250000000000) x202 := by
    exact hx201
  let x203 : ℝ := biasE (45879 / 250000)
  have hx203 : Bounds (338106151681 / 500000000000) (169053076341 / 250000000000) x203 := by
    simpa +zetaDelta only [biasE, div_one] using hx202
  let x204 : ℝ := Real.log (2 / 1)
  have hx204 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x204 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x205 : ℝ := (1 / 1)+(229 / 1250)
  have hx205 : Bounds (1479 / 1250) (1479 / 1250) x205 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((229 / 1250) : ℝ)) <;> norm_num
  let x206 : ℝ := (1 / 1)+(229 / 1250)
  have hx206 : Bounds (1479 / 1250) (1479 / 1250) x206 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((229 / 1250) : ℝ)) <;> norm_num
  let x207 : ℝ := Real.log x206
  have hx207 : Bounds (21027829 / 125000000) (168222633 / 1000000000) x207 := by
    exact bounds_log hx206 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x208 : ℝ := x205*x207
  have hx208 : Bounds (99520509091 / 500000000000) (99520509683 / 500000000000) x208 := by
    apply bounds_mul hx205 hx207 <;> norm_num
  let x209 : ℝ := -(229 / 1250)
  have hx209 : Bounds (-229 / 1250) (-229 / 1250) x209 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((229 / 1250) : ℝ))
  let x210 : ℝ := (1 / 1)+x209
  have hx210 : Bounds (1021 / 1250) (1021 / 1250) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx209 <;> norm_num
  let x211 : ℝ := (1 / 1)-(229 / 1250)
  have hx211 : Bounds (1021 / 1250) (1021 / 1250) x211 := by
    exact hx210
  let x212 : ℝ := -(229 / 1250)
  have hx212 : Bounds (-229 / 1250) (-229 / 1250) x212 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((229 / 1250) : ℝ))
  let x213 : ℝ := (1 / 1)+x212
  have hx213 : Bounds (1021 / 1250) (1021 / 1250) x213 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx212 <;> norm_num
  let x214 : ℝ := (1 / 1)-(229 / 1250)
  have hx214 : Bounds (1021 / 1250) (1021 / 1250) x214 := by
    exact hx213
  let x215 : ℝ := Real.log x214
  have hx215 : Bounds (-202361013 / 1000000000) (-50590253 / 250000000) x215 := by
    exact bounds_log hx214 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x216 : ℝ := x211*x215
  have hx216 : Bounds (-165288475419 / 1000000000000) (-165288474601 / 1000000000000) x216 := by
    apply bounds_mul hx211 hx215 <;> norm_num
  let x217 : ℝ := x208+x216
  have hx217 : Bounds (33752542763 / 1000000000000) (6750508953 / 200000000000) x217 := by
    apply bounds_add hx208 hx216 <;> norm_num
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (16876271381 / 1000000000000) (16876272383 / 1000000000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (16876271381 / 1000000000000) (16876272383 / 1000000000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := -x220
  have hx221 : Bounds (-16876272383 / 1000000000000) (-16876271381 / 1000000000000) x221 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx220
  let x222 : ℝ := x204+x221
  have hx222 : Bounds (676270907617 / 1000000000000) (676270909619 / 1000000000000) x222 := by
    apply bounds_add hx204 hx221 <;> norm_num
  let x223 : ℝ := x204-x220
  have hx223 : Bounds (676270907617 / 1000000000000) (676270909619 / 1000000000000) x223 := by
    exact hx222
  let x224 : ℝ := biasE (229 / 1250)
  have hx224 : Bounds (676270907617 / 1000000000000) (676270909619 / 1000000000000) x224 := by
    simpa +zetaDelta only [biasE, div_one] using hx223
  let x225 : ℝ := biasE c
  have hx225 : Bounds (338106151681 / 500000000000) (676270909619 / 1000000000000) x225 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx203.1 hx224.2
  let x226 : ℝ := x159⁻¹
  have hx226 : Bounds (959311434801 / 250000000000) (3843901866677 / 1000000000000) x226 := by
    apply bounds_inv hx159 <;> norm_num
  let x227 : ℝ := x148*x226
  have hx227 : Bounds (718284350469 / 500000000000) (360411049453 / 250000000000) x227 := by
    apply bounds_mul hx148 hx226 <;> norm_num
  let x228 : ℝ := x148/x159
  have hx228 : Bounds (718284350469 / 500000000000) (360411049453 / 250000000000) x228 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx227
  let x229 : ℝ := c*x148
  have hx229 : Bounds (17146372939 / 250000000000) (34413570609 / 500000000000) x229 := by
    apply bounds_mul hc hx148 <;> norm_num
  let x230 : ℝ := x225+x229
  have hx230 : Bounds (372398897559 / 500000000000) (745098050837 / 1000000000000) x230 := by
    apply bounds_add hx225 hx229 <;> norm_num
  let x231 : ℝ := x*x170
  have hx231 : Bounds (33149865029 / 1000000000000) (33262746813 / 1000000000000) x231 := by
    apply bounds_mul hx hx170 <;> norm_num
  let x232 : ℝ := x48+x231
  have hx232 : Bounds (693459250043 / 1000000000000) (693681912021 / 1000000000000) x232 := by
    apply bounds_add hx48 hx231 <;> norm_num
  let x233 : ℝ := x232⁻¹
  have hx233 : Bounds (1441582925359 / 1000000000000) (1442045801449 / 1000000000000) x233 := by
    apply bounds_inv hx232 <;> norm_num
  let x234 : ℝ := x230*x233
  have hx234 : Bounds (1073687784287 / 1000000000000) (537232757939 / 500000000000) x234 := by
    apply bounds_mul hx230 hx233 <;> norm_num
  let x235 : ℝ := x230/x232
  have hx235 : Bounds (1073687784287 / 1000000000000) (537232757939 / 500000000000) x235 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx234
  let x236 : ℝ := y*y
  have hx236 : Bounds (16184673961 / 250000000000) (162384049 / 2500000000) x236 := by
    apply bounds_mul hy hy <;> norm_num
  let x237 : ℝ := -x236
  have hx237 : Bounds (-162384049 / 2500000000) (-16184673961 / 250000000000) x237 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx236
  let x238 : ℝ := (1 / 1)+x237
  have hx238 : Bounds (2337615951 / 2500000000) (233815326039 / 250000000000) x238 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx237 <;> norm_num
  let x239 : ℝ := (1 / 1)-x236
  have hx239 : Bounds (2337615951 / 2500000000) (233815326039 / 250000000000) x239 := by
    exact hx238
  let x240 : ℝ := x239*x159
  have hx240 : Bounds (243254487973 / 1000000000000) (243732449711 / 1000000000000) x240 := by
    apply bounds_mul hx239 hx159 <;> norm_num
  let x241 : ℝ := c*c
  have hx241 : Bounds (52441 / 1562500) (2104882641 / 62500000000) x241 := by
    apply bounds_mul hc hc <;> norm_num
  let x242 : ℝ := -x241
  have hx242 : Bounds (-2104882641 / 62500000000) (-52441 / 1562500) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx241
  let x243 : ℝ := (1 / 1)+x242
  have hx243 : Bounds (60395117359 / 62500000000) (1510059 / 1562500) x243 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx242 <;> norm_num
  let x244 : ℝ := (1 / 1)-x241
  have hx244 : Bounds (60395117359 / 62500000000) (1510059 / 1562500) x244 := by
    exact hx243
  let x245 : ℝ := x244*x182
  have hx245 : Bounds (686297615779 / 1000000000000) (343218931707 / 500000000000) x245 := by
    apply bounds_mul hx244 hx182 <;> norm_num
  let x246 : ℝ := y*y
  have hx246 : Bounds (16184673961 / 250000000000) (162384049 / 2500000000) x246 := by
    apply bounds_mul hy hy <;> norm_num
  let x247 : ℝ := (1 / 1)+x246
  have hx247 : Bounds (266184673961 / 250000000000) (2662384049 / 2500000000) x247 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx246 <;> norm_num
  let x248 : ℝ := x247*x159
  have hx248 : Bounds (276994245111 / 1000000000000) (8672835381 / 31250000000) x248 := by
    apply bounds_mul hx247 hx159 <;> norm_num
  let x249 : ℝ := -y
  have hx249 : Bounds (-12743 / 50000) (-127219 / 500000) x249 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x250 : ℝ := x248+x249
  have hx250 : Bounds (22134245111 / 1000000000000) (721647881 / 31250000000) x250 := by
    apply bounds_add hx248 hx249 <;> norm_num
  let x251 : ℝ := x248-y
  have hx251 : Bounds (22134245111 / 1000000000000) (721647881 / 31250000000) x251 := by
    exact hx250
  let x252 : ℝ := x240*x240
  have hx252 : Bounds (59172745919 / 1000000000000) (59405507043 / 1000000000000) x252 := by
    apply bounds_mul hx240 hx240 <;> norm_num
  let x253 : ℝ := x252⁻¹
  have hx253 : Bounds (16833456185739 / 1000000000000) (16899672044439 / 1000000000000) x253 := by
    apply bounds_inv hx252 <;> norm_num
  let x254 : ℝ := x251*x253
  have hx254 : Bounds (2328724033 / 6250000000) (78051920131 / 200000000000) x254 := by
    apply bounds_mul hx251 hx253 <;> norm_num
  let x255 : ℝ := x251/x252
  have hx255 : Bounds (2328724033 / 6250000000) (78051920131 / 200000000000) x255 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx254
  let x256 : ℝ := (-2 / 1)*x255
  have hx256 : Bounds (-78051920131 / 100000000000) (-2328724033 / 3125000000) x256 := by
    apply bounds_mul (bounds_const ((-2 / 1) : ℝ)) hx255 <;> norm_num
  let x257 : ℝ := x256*x228
  have hx257 : Bounds (-22504619557 / 20000000000) (-1070519058857 / 1000000000000) x257 := by
    apply bounds_mul hx256 hx228 <;> norm_num
  let x258 : ℝ := (2 / 1)*x182
  have hx258 : Bounds (1420432739 / 1000000000) (88784541 / 62500000) x258 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx182 <;> norm_num
  let x259 : ℝ := c*c
  have hx259 : Bounds (52441 / 1562500) (2104882641 / 62500000000) x259 := by
    apply bounds_mul hc hc <;> norm_num
  let x260 : ℝ := -x259
  have hx260 : Bounds (-2104882641 / 62500000000) (-52441 / 1562500) x260 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx259
  let x261 : ℝ := x258+x260
  have hx261 : Bounds (173344327093 / 125000000000) (86686901 / 62500000) x261 := by
    apply bounds_add hx258 hx260 <;> norm_num
  let x262 : ℝ := x258-x259
  have hx262 : Bounds (173344327093 / 125000000000) (86686901 / 62500000) x262 := by
    exact hx261
  let x263 : ℝ := c*x262
  have hx263 : Bounds (254053445787 / 1000000000000) (254534933183 / 1000000000000) x263 := by
    apply bounds_mul hc hx262 <;> norm_num
  let x264 : ℝ := x245*x245
  have hx264 : Bounds (471004417423 / 1000000000000) (471196940329 / 1000000000000) x264 := by
    apply bounds_mul hx245 hx245 <;> norm_num
  let x265 : ℝ := x264⁻¹
  have hx265 : Bounds (2122254867151 / 1000000000000) (424624467631 / 200000000000) x265 := by
    apply bounds_inv hx264 <;> norm_num
  let x266 : ℝ := x263*x265
  have hx266 : Bounds (539166161837 / 1000000000000) (270204401241 / 500000000000) x266 := by
    apply bounds_mul hx263 hx265 <;> norm_num
  let x267 : ℝ := x263/x264
  have hx267 : Bounds (539166161837 / 1000000000000) (270204401241 / 500000000000) x267 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx266
  let x268 : ℝ := (2 / 1)*x267
  have hx268 : Bounds (539166161837 / 500000000000) (270204401241 / 250000000000) x268 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx267 <;> norm_num
  let x269 : ℝ := x268*x235
  have hx269 : Bounds (115779224333 / 100000000000) (72581327843 / 62500000000) x269 := by
    apply bounds_mul hx268 hx235 <;> norm_num
  let x270 : ℝ := x257+x269
  have hx270 : Bounds (814031637 / 25000000000) (90782186631 / 1000000000000) x270 := by
    apply bounds_add hx257 hx269 <;> norm_num
  have hPos : 0 < x270 :=
    lt_of_lt_of_le (by norm_num) hx270.1
  have hBridgeL : doubleCapBridgeL x = x48 := by
    exact hEll'
  rw [← doubleCapBridgeDerivativeTraceForm_eq x]
  simpa +zetaDelta only [doubleCapBridgeDerivativeTraceForm,
    hBridgeL, SmallMean.A, biasB, div_one, pow_two] using hPos

theorem acceptedCell : DoubleCapBridgeDerivativeCellCertificate
    (⟨184, by decide⟩ : Fin 256) doubleCapBridgeDerivativeExpression where
  positive x hx := by
    have hloEq : doubleCapBridgeLo (⟨184, by decide⟩ : Fin 256) =
        (229 / 1280) := by norm_num [doubleCapBridgeLo, doubleCapBridgeStep]
    have hhiEq : doubleCapBridgeHi (⟨184, by decide⟩ : Fin 256) =
        (367 / 2048) := by norm_num [doubleCapBridgeHi, doubleCapBridgeStep]
    have hlo : (229 / 1280) ≤ x := by
      simpa only [hloEq] using hx.1
    have hhi : x ≤ (367 / 2048) := by
      simpa only [hhiEq] using hx.2
    exact cell_derivative_pos x ⟨hlo, hhi⟩

#print axioms cell_derivative_pos
#print axioms acceptedCell

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell184

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell185 =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell185
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_derivative_pos (x : ℝ)
    (hx : Bounds (367 / 2048) (919 / 5120) x) :
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
  have hx0 : Bounds (367 / 1024) (919 / 2560) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx <;> norm_num
  let x1 : ℝ := Real.log (2 / 1)
  have hx1 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x1 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x2 : ℝ := Real.log (2 / 1)
  have hx2 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x2 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x3 : ℝ := (1 / 1)+(919 / 2560)
  have hx3 : Bounds (3479 / 2560) (3479 / 2560) x3 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((919 / 2560) : ℝ)) <;> norm_num
  let x4 : ℝ := (1 / 1)+(919 / 2560)
  have hx4 : Bounds (3479 / 2560) (3479 / 2560) x4 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((919 / 2560) : ℝ)) <;> norm_num
  let x5 : ℝ := Real.log x4
  have hx5 : Bounds (306737637 / 1000000000) (153368819 / 500000000) x5 := by
    exact bounds_log hx4 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x6 : ℝ := x3*x5
  have hx6 : Bounds (416851655907 / 1000000000000) (416851657267 / 1000000000000) x6 := by
    apply bounds_mul hx3 hx5 <;> norm_num
  let x7 : ℝ := -(919 / 2560)
  have hx7 : Bounds (-919 / 2560) (-919 / 2560) x7 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((919 / 2560) : ℝ))
  let x8 : ℝ := (1 / 1)+x7
  have hx8 : Bounds (1641 / 2560) (1641 / 2560) x8 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx7 <;> norm_num
  let x9 : ℝ := (1 / 1)-(919 / 2560)
  have hx9 : Bounds (1641 / 2560) (1641 / 2560) x9 := by
    exact hx8
  let x10 : ℝ := -(919 / 2560)
  have hx10 : Bounds (-919 / 2560) (-919 / 2560) x10 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((919 / 2560) : ℝ))
  let x11 : ℝ := (1 / 1)+x10
  have hx11 : Bounds (1641 / 2560) (1641 / 2560) x11 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx10 <;> norm_num
  let x12 : ℝ := (1 / 1)-(919 / 2560)
  have hx12 : Bounds (1641 / 2560) (1641 / 2560) x12 := by
    exact hx11
  let x13 : ℝ := Real.log x12
  have hx13 : Bounds (-444701447 / 1000000000) (-222350723 / 500000000) x13 := by
    exact bounds_log hx12 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x14 : ℝ := x9*x13
  have hx14 : Bounds (-71265143997 / 250000000000) (-142530287673 / 500000000000) x14 := by
    apply bounds_mul hx9 hx13 <;> norm_num
  let x15 : ℝ := x6+x14
  have hx15 : Bounds (131791079919 / 1000000000000) (131791081921 / 1000000000000) x15 := by
    apply bounds_add hx6 hx14 <;> norm_num
  let x16 : ℝ := (2 / 1)⁻¹
  have hx16 : Bounds (1 / 2) (1 / 2) x16 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x17 : ℝ := x15*x16
  have hx17 : Bounds (65895539959 / 1000000000000) (65895540961 / 1000000000000) x17 := by
    apply bounds_mul hx15 hx16 <;> norm_num
  let x18 : ℝ := x15/(2 / 1)
  have hx18 : Bounds (65895539959 / 1000000000000) (65895540961 / 1000000000000) x18 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx17
  let x19 : ℝ := -x18
  have hx19 : Bounds (-65895540961 / 1000000000000) (-65895539959 / 1000000000000) x19 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx18
  let x20 : ℝ := x2+x19
  have hx20 : Bounds (627251639039 / 1000000000000) (627251641041 / 1000000000000) x20 := by
    apply bounds_add hx2 hx19 <;> norm_num
  let x21 : ℝ := x2-x18
  have hx21 : Bounds (627251639039 / 1000000000000) (627251641041 / 1000000000000) x21 := by
    exact hx20
  let x22 : ℝ := biasE (919 / 2560)
  have hx22 : Bounds (627251639039 / 1000000000000) (627251641041 / 1000000000000) x22 := by
    simpa +zetaDelta only [biasE, div_one] using hx21
  let x23 : ℝ := Real.log (2 / 1)
  have hx23 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x23 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x24 : ℝ := (1 / 1)+(367 / 1024)
  have hx24 : Bounds (1391 / 1024) (1391 / 1024) x24 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((367 / 1024) : ℝ)) <;> norm_num
  let x25 : ℝ := (1 / 1)+(367 / 1024)
  have hx25 : Bounds (1391 / 1024) (1391 / 1024) x25 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((367 / 1024) : ℝ)) <;> norm_num
  let x26 : ℝ := Real.log x25
  have hx26 : Bounds (153153193 / 500000000) (306306387 / 1000000000) x26 := by
    exact bounds_log hx25 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x27 : ℝ := x24*x26
  have hx27 : Bounds (208043058069 / 500000000000) (208043058749 / 500000000000) x27 := by
    apply bounds_mul hx24 hx26 <;> norm_num
  let x28 : ℝ := -(367 / 1024)
  have hx28 : Bounds (-367 / 1024) (-367 / 1024) x28 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((367 / 1024) : ℝ))
  let x29 : ℝ := (1 / 1)+x28
  have hx29 : Bounds (657 / 1024) (657 / 1024) x29 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx28 <;> norm_num
  let x30 : ℝ := (1 / 1)-(367 / 1024)
  have hx30 : Bounds (657 / 1024) (657 / 1024) x30 := by
    exact hx29
  let x31 : ℝ := -(367 / 1024)
  have hx31 : Bounds (-367 / 1024) (-367 / 1024) x31 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((367 / 1024) : ℝ))
  let x32 : ℝ := (1 / 1)+x31
  have hx32 : Bounds (657 / 1024) (657 / 1024) x32 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx31 <;> norm_num
  let x33 : ℝ := (1 / 1)-(367 / 1024)
  have hx33 : Bounds (657 / 1024) (657 / 1024) x33 := by
    exact hx32
  let x34 : ℝ := Real.log x33
  have hx34 : Bounds (-110946947 / 250000000) (-443787787 / 1000000000) x34 := by
    exact bounds_log hx33 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x35 : ℝ := x30*x34
  have hx35 : Bounds (-1423674691 / 5000000000) (-284734937557 / 1000000000000) x35 := by
    apply bounds_mul hx30 hx34 <;> norm_num
  let x36 : ℝ := x27+x35
  have hx36 : Bounds (65675588969 / 500000000000) (131351179941 / 1000000000000) x36 := by
    apply bounds_add hx27 hx35 <;> norm_num
  let x37 : ℝ := (2 / 1)⁻¹
  have hx37 : Bounds (1 / 2) (1 / 2) x37 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x38 : ℝ := x36*x37
  have hx38 : Bounds (65675588969 / 1000000000000) (65675589971 / 1000000000000) x38 := by
    apply bounds_mul hx36 hx37 <;> norm_num
  let x39 : ℝ := x36/(2 / 1)
  have hx39 : Bounds (65675588969 / 1000000000000) (65675589971 / 1000000000000) x39 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx38
  let x40 : ℝ := -x39
  have hx40 : Bounds (-65675589971 / 1000000000000) (-65675588969 / 1000000000000) x40 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx39
  let x41 : ℝ := x23+x40
  have hx41 : Bounds (627471590029 / 1000000000000) (627471592031 / 1000000000000) x41 := by
    apply bounds_add hx23 hx40 <;> norm_num
  let x42 : ℝ := x23-x39
  have hx42 : Bounds (627471590029 / 1000000000000) (627471592031 / 1000000000000) x42 := by
    exact hx41
  let x43 : ℝ := biasE (367 / 1024)
  have hx43 : Bounds (627471590029 / 1000000000000) (627471592031 / 1000000000000) x43 := by
    simpa +zetaDelta only [biasE, div_one] using hx42
  let x44 : ℝ := biasE x0
  have hx44 : Bounds (627251639039 / 1000000000000) (627471592031 / 1000000000000) x44 := by
    exact bounds_biasE hx0 (by norm_num) (by norm_num) hx22.1 hx43.2
  let x45 : ℝ := x1+x44
  have hx45 : Bounds (1320398819039 / 1000000000000) (1320618773031 / 1000000000000) x45 := by
    apply bounds_add hx1 hx44 <;> norm_num
  let x46 : ℝ := (2 / 1)⁻¹
  have hx46 : Bounds (1 / 2) (1 / 2) x46 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x47 : ℝ := x45*x46
  have hx47 : Bounds (660199409519 / 1000000000000) (165077346629 / 250000000000) x47 := by
    apply bounds_mul hx45 hx46 <;> norm_num
  let x48 : ℝ := x45/(2 / 1)
  have hx48 : Bounds (660199409519 / 1000000000000) (165077346629 / 250000000000) x48 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx47
  let x49 : ℝ := Real.log (2 / 1)
  have hx49 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x49 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x50 : ℝ := (1 / 1)+(254859 / 1000000)
  have hx50 : Bounds (1254859 / 1000000) (1254859 / 1000000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((254859 / 1000000) : ℝ)) <;> norm_num
  let x51 : ℝ := (1 / 1)+(254859 / 1000000)
  have hx51 : Bounds (1254859 / 1000000) (1254859 / 1000000) x51 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((254859 / 1000000) : ℝ)) <;> norm_num
  let x52 : ℝ := Real.log x51
  have hx52 : Bounds (45404643 / 200000000) (14188951 / 62500000) x52 := by
    exact bounds_log hx51 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x53 : ℝ := x50*x52
  have hx53 : Bounds (284882124551 / 1000000000000) (284882125807 / 1000000000000) x53 := by
    apply bounds_mul hx50 hx52 <;> norm_num
  let x54 : ℝ := -(254859 / 1000000)
  have hx54 : Bounds (-254859 / 1000000) (-254859 / 1000000) x54 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((254859 / 1000000) : ℝ))
  let x55 : ℝ := (1 / 1)+x54
  have hx55 : Bounds (745141 / 1000000) (745141 / 1000000) x55 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx54 <;> norm_num
  let x56 : ℝ := (1 / 1)-(254859 / 1000000)
  have hx56 : Bounds (745141 / 1000000) (745141 / 1000000) x56 := by
    exact hx55
  let x57 : ℝ := -(254859 / 1000000)
  have hx57 : Bounds (-254859 / 1000000) (-254859 / 1000000) x57 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((254859 / 1000000) : ℝ))
  let x58 : ℝ := (1 / 1)+x57
  have hx58 : Bounds (745141 / 1000000) (745141 / 1000000) x58 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx57 <;> norm_num
  let x59 : ℝ := (1 / 1)-(254859 / 1000000)
  have hx59 : Bounds (745141 / 1000000) (745141 / 1000000) x59 := by
    exact hx58
  let x60 : ℝ := Real.log x59
  have hx60 : Bounds (-294181817 / 1000000000) (-36772727 / 125000000) x60 := by
    exact bounds_log hx59 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x61 : ℝ := x56*x60
  have hx61 : Bounds (-109603466651 / 500000000000) (-54801733139 / 250000000000) x61 := by
    apply bounds_mul hx56 hx60 <;> norm_num
  let x62 : ℝ := x53+x61
  have hx62 : Bounds (65675191249 / 1000000000000) (65675193251 / 1000000000000) x62 := by
    apply bounds_add hx53 hx61 <;> norm_num
  let x63 : ℝ := (2 / 1)⁻¹
  have hx63 : Bounds (1 / 2) (1 / 2) x63 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x64 : ℝ := x62*x63
  have hx64 : Bounds (4104699453 / 125000000000) (16418798313 / 500000000000) x64 := by
    apply bounds_mul hx62 hx63 <;> norm_num
  let x65 : ℝ := x62/(2 / 1)
  have hx65 : Bounds (4104699453 / 125000000000) (16418798313 / 500000000000) x65 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx64
  let x66 : ℝ := -x65
  have hx66 : Bounds (-16418798313 / 500000000000) (-4104699453 / 125000000000) x66 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx65
  let x67 : ℝ := x49+x66
  have hx67 : Bounds (330154791687 / 500000000000) (20634674543 / 31250000000) x67 := by
    apply bounds_add hx49 hx66 <;> norm_num
  let x68 : ℝ := x49-x65
  have hx68 : Bounds (330154791687 / 500000000000) (20634674543 / 31250000000) x68 := by
    exact hx67
  let x69 : ℝ := biasE (254859 / 1000000)
  have hx69 : Bounds (330154791687 / 500000000000) (20634674543 / 31250000000) x69 := by
    simpa +zetaDelta only [biasE, div_one] using hx68
  let x70 : ℝ := Real.log (2 / 1)
  have hx70 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x70 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x71 : ℝ := (1 / 1)+(127641 / 500000)
  have hx71 : Bounds (627641 / 500000) (627641 / 500000) x71 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((127641 / 500000) : ℝ)) <;> norm_num
  let x72 : ℝ := (1 / 1)+(127641 / 500000)
  have hx72 : Bounds (627641 / 500000) (627641 / 500000) x72 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((127641 / 500000) : ℝ)) <;> norm_num
  let x73 : ℝ := Real.log x72
  have hx73 : Bounds (28420031 / 125000000) (227360249 / 1000000000) x73 := by
    exact bounds_log hx72 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x74 : ℝ := x71*x73
  have hx74 : Bounds (285401226829 / 1000000000000) (142700614043 / 500000000000) x74 := by
    apply bounds_mul hx71 hx73 <;> norm_num
  let x75 : ℝ := -(127641 / 500000)
  have hx75 : Bounds (-127641 / 500000) (-127641 / 500000) x75 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((127641 / 500000) : ℝ))
  let x76 : ℝ := (1 / 1)+x75
  have hx76 : Bounds (372359 / 500000) (372359 / 500000) x76 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx75 <;> norm_num
  let x77 : ℝ := (1 / 1)-(127641 / 500000)
  have hx77 : Bounds (372359 / 500000) (372359 / 500000) x77 := by
    exact hx76
  let x78 : ℝ := -(127641 / 500000)
  have hx78 : Bounds (-127641 / 500000) (-127641 / 500000) x78 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((127641 / 500000) : ℝ))
  let x79 : ℝ := (1 / 1)+x78
  have hx79 : Bounds (372359 / 500000) (372359 / 500000) x79 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx78 <;> norm_num
  let x80 : ℝ := (1 / 1)-(127641 / 500000)
  have hx80 : Bounds (372359 / 500000) (372359 / 500000) x80 := by
    exact hx79
  let x81 : ℝ := Real.log x80
  have hx81 : Bounds (-36843707 / 125000000) (-58949931 / 200000000) x81 := by
    exact bounds_log hx80 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x82 : ℝ := x77*x81
  have hx82 : Bounds (-109752687159 / 500000000000) (-54876343393 / 250000000000) x82 := by
    apply bounds_mul hx77 hx81 <;> norm_num
  let x83 : ℝ := x74+x82
  have hx83 : Bounds (65895852511 / 1000000000000) (32947927257 / 500000000000) x83 := by
    apply bounds_add hx74 hx82 <;> norm_num
  let x84 : ℝ := (2 / 1)⁻¹
  have hx84 : Bounds (1 / 2) (1 / 2) x84 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x85 : ℝ := x83*x84
  have hx85 : Bounds (6589585251 / 200000000000) (32947927257 / 1000000000000) x85 := by
    apply bounds_mul hx83 hx84 <;> norm_num
  let x86 : ℝ := x83/(2 / 1)
  have hx86 : Bounds (6589585251 / 200000000000) (32947927257 / 1000000000000) x86 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx85
  let x87 : ℝ := -x86
  have hx87 : Bounds (-32947927257 / 1000000000000) (-6589585251 / 200000000000) x87 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx86
  let x88 : ℝ := x70+x87
  have hx88 : Bounds (660199252743 / 1000000000000) (132039850949 / 200000000000) x88 := by
    apply bounds_add hx70 hx87 <;> norm_num
  let x89 : ℝ := x70-x86
  have hx89 : Bounds (660199252743 / 1000000000000) (132039850949 / 200000000000) x89 := by
    exact hx88
  let x90 : ℝ := biasE (127641 / 500000)
  have hx90 : Bounds (660199252743 / 1000000000000) (132039850949 / 200000000000) x90 := by
    simpa +zetaDelta only [biasE, div_one] using hx89
  let y : ℝ := doubleCapHighTailY x
  have hEll' : Real.log 2 * doubleCapHighTailFloor x = x48 := by
    simpa +zetaDelta only [div_one] using hEll
  have hy : Bounds (254859 / 1000000) (127641 / 500000) y := by
    dsimp only [y, doubleCapHighTailY]
    apply entropyInverseBias_bracket hh0.le hh1.le
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (127641 / 500000) ≤ (132039850949 / 200000000000) := hx90.2
      have h2 : (660199409519 / 1000000000000) ≤ x48 := hx48.1
      linarith [hEll']
    · have h1 : x48 ≤ (165077346629 / 250000000000) := hx48.2
      have h2 : (330154791687 / 500000000000) ≤ biasE (254859 / 1000000) := hx69.1
      linarith [hEll']
  let x91 : ℝ := x⁻¹
  have hx91 : Bounds (5571273122959 / 1000000000000) (558038147139 / 100000000000) x91 := by
    apply bounds_inv hx <;> norm_num
  let x92 : ℝ := x48*x91
  have hx92 : Bounds (1839075613023 / 500000000000) (3684778265899 / 1000000000000) x92 := by
    apply bounds_mul hx48 hx91 <;> norm_num
  let x93 : ℝ := x48/x
  have hx93 : Bounds (1839075613023 / 500000000000) (3684778265899 / 1000000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(36703 / 200000)
  have hx95 : Bounds (236703 / 200000) (236703 / 200000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((36703 / 200000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(36703 / 200000)
  have hx96 : Bounds (236703 / 200000) (236703 / 200000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((36703 / 200000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (21061103 / 125000000) (6739553 / 40000000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (24926131317 / 125000000000) (4985226293 / 25000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(36703 / 200000)
  have hx99 : Bounds (-36703 / 200000) (-36703 / 200000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((36703 / 200000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (163297 / 200000) (163297 / 200000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(36703 / 200000)
  have hx101 : Bounds (163297 / 200000) (163297 / 200000) x101 := by
    exact hx100
  let x102 : ℝ := -(36703 / 200000)
  have hx102 : Bounds (-36703 / 200000) (-36703 / 200000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((36703 / 200000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (163297 / 200000) (163297 / 200000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(36703 / 200000)
  have hx104 : Bounds (163297 / 200000) (163297 / 200000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-101373369 / 500000000) (-202746737 / 1000000000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-20692458797 / 125000000000) (-165539669559 / 1000000000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (105841813 / 3125000000) (33869382161 / 1000000000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (105841813 / 6250000000) (16934691081 / 1000000000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (105841813 / 6250000000) (16934691081 / 1000000000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-16934691081 / 1000000000000) (-105841813 / 6250000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (676212488919 / 1000000000000) (16905312273 / 25000000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (676212488919 / 1000000000000) (16905312273 / 25000000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (36703 / 200000)
  have hx114 : Bounds (676212488919 / 1000000000000) (16905312273 / 25000000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(18383 / 100000)
  have hx116 : Bounds (118383 / 100000) (118383 / 100000) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((18383 / 100000) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(18383 / 100000)
  have hx117 : Bounds (118383 / 100000) (118383 / 100000) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((18383 / 100000) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (33750989 / 200000000) (84377473 / 500000000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (199777166539 / 1000000000000) (49944291931 / 250000000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(18383 / 100000)
  have hx120 : Bounds (-18383 / 100000) (-18383 / 100000) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((18383 / 100000) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (81617 / 100000) (81617 / 100000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(18383 / 100000)
  have hx122 : Bounds (81617 / 100000) (81617 / 100000) x122 := by
    exact hx121
  let x123 : ℝ := -(18383 / 100000)
  have hx123 : Bounds (-18383 / 100000) (-18383 / 100000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((18383 / 100000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (81617 / 100000) (81617 / 100000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(18383 / 100000)
  have hx125 : Bounds (81617 / 100000) (81617 / 100000) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-203132613 / 1000000000) (-50783153 / 250000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-165790744753 / 1000000000000) (-1295240187 / 7812500000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (16993210893 / 500000000000) (8496605947 / 250000000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (16993210893 / 1000000000000) (8496605947 / 500000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (16993210893 / 1000000000000) (8496605947 / 500000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-8496605947 / 500000000000) (-16993210893 / 1000000000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (338076984053 / 500000000000) (676153970107 / 1000000000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (338076984053 / 500000000000) (676153970107 / 1000000000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (18383 / 100000)
  have hx135 : Bounds (338076984053 / 500000000000) (676153970107 / 1000000000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(36703 / 200000)
  have hx136 : Bounds (674995922247 / 1000000000000) (676212083467 / 1000000000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((36703 / 200000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(18383 / 100000)
  have hx137 : Bounds (169038634971 / 250000000000) (677372788621 / 1000000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((18383 / 100000) : ℝ)) <;> norm_num
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
  have hc : Bounds (36703 / 200000) (18383 / 100000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num)
      (by norm_num) (show 0 < x93 by linarith [hx93.1]) hcEq
    · have h1 : x93 * (36703 / 200000) ≤ (676212083467 / 1000000000000) := hx136.2
      have h2 : (676212488919 / 1000000000000) ≤ biasE (36703 / 200000) := hx114.1
      linarith
    · have h1 : biasE (18383 / 100000) ≤ (676153970107 / 1000000000000) := hx135.2
      have h2 : (169038634971 / 250000000000) ≤ x93 * (18383 / 100000) := hx137.1
      linarith
  let x138 : ℝ := (1 / 1)+x0
  have hx138 : Bounds (1391 / 1024) (3479 / 2560) x138 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx0 <;> norm_num
  let x139 : ℝ := -x0
  have hx139 : Bounds (-919 / 2560) (-367 / 1024) x139 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x140 : ℝ := (1 / 1)+x139
  have hx140 : Bounds (1641 / 2560) (657 / 1024) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx139 <;> norm_num
  let x141 : ℝ := (1 / 1)-x0
  have hx141 : Bounds (1641 / 2560) (657 / 1024) x141 := by
    exact hx140
  let x142 : ℝ := x141⁻¹
  have hx142 : Bounds (311719939117 / 200000000000) (1560024375381 / 1000000000000) x142 := by
    apply bounds_inv hx141 <;> norm_num
  let x143 : ℝ := x138*x142
  have hx143 : Bounds (211719939117 / 100000000000) (1060024375381 / 500000000000) x143 := by
    apply bounds_mul hx138 hx142 <;> norm_num
  let x144 : ℝ := x138/x141
  have hx144 : Bounds (211719939117 / 100000000000) (1060024375381 / 500000000000) x144 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx143
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (187523543 / 250000000) (150287817 / 200000000) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_14.2)
  let x146 : ℝ := (2 / 1)⁻¹
  have hx146 : Bounds (1 / 2) (1 / 2) x146 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x147 : ℝ := x145*x146
  have hx147 : Bounds (187523543 / 500000000) (150287817 / 400000000) x147 := by
    apply bounds_mul hx145 hx146 <;> norm_num
  let x148 : ℝ := x145/(2 / 1)
  have hx148 : Bounds (187523543 / 500000000) (150287817 / 400000000) x148 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx147
  let x149 : ℝ := (1 / 1)+y
  have hx149 : Bounds (1254859 / 1000000) (627641 / 500000) x149 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x150 : ℝ := -y
  have hx150 : Bounds (-127641 / 500000) (-254859 / 1000000) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (372359 / 500000) (745141 / 1000000) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-y
  have hx152 : Bounds (372359 / 500000) (745141 / 1000000) x152 := by
    exact hx151
  let x153 : ℝ := x152⁻¹
  have hx153 : Bounds (268405576931 / 200000000000) (335697539203 / 250000000000) x153 := by
    apply bounds_inv hx152 <;> norm_num
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (168405576931 / 100000000000) (210697539203 / 125000000000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x149/x152
  have hx155 : Bounds (168405576931 / 100000000000) (210697539203 / 125000000000) x155 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx154
  let x156 : ℝ := Real.log x155
  have hx156 : Bounds (65150629 / 125000000) (104421981 / 200000000) x156 := by
    exact bounds_log hx155 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_16.2)
  let x157 : ℝ := (2 / 1)⁻¹
  have hx157 : Bounds (1 / 2) (1 / 2) x157 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x158 : ℝ := x156*x157
  have hx158 : Bounds (65150629 / 250000000) (104421981 / 400000000) x158 := by
    apply bounds_mul hx156 hx157 <;> norm_num
  let x159 : ℝ := x156/(2 / 1)
  have hx159 : Bounds (65150629 / 250000000) (104421981 / 400000000) x159 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx158
  let x160 : ℝ := (1 / 1)+c
  have hx160 : Bounds (236703 / 200000) (118383 / 100000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x161 : ℝ := -c
  have hx161 : Bounds (-18383 / 100000) (-36703 / 200000) x161 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x162 : ℝ := (1 / 1)+x161
  have hx162 : Bounds (81617 / 100000) (163297 / 200000) x162 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx161 <;> norm_num
  let x163 : ℝ := (1 / 1)-c
  have hx163 : Bounds (81617 / 100000) (163297 / 200000) x163 := by
    exact hx162
  let x164 : ℝ := x163⁻¹
  have hx164 : Bounds (1224762243029 / 1000000000000) (3063087347 / 2500000000) x164 := by
    apply bounds_inv hx163 <;> norm_num
  let x165 : ℝ := x160*x164
  have hx165 : Bounds (724762243029 / 500000000000) (1813087347 / 1250000000) x165 := by
    apply bounds_mul hx160 hx164 <;> norm_num
  let x166 : ℝ := x160/x163
  have hx166 : Bounds (724762243029 / 500000000000) (1813087347 / 1250000000) x166 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx165
  let x167 : ℝ := Real.log x166
  have hx167 : Bounds (371235561 / 1000000000) (185943779 / 500000000) x167 := by
    exact bounds_log hx166 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x168 : ℝ := (2 / 1)⁻¹
  have hx168 : Bounds (1 / 2) (1 / 2) x168 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x169 : ℝ := x167*x168
  have hx169 : Bounds (371235561 / 2000000000) (185943779 / 1000000000) x169 := by
    apply bounds_mul hx167 hx168 <;> norm_num
  let x170 : ℝ := x167/(2 / 1)
  have hx170 : Bounds (371235561 / 2000000000) (185943779 / 1000000000) x170 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx169
  let x171 : ℝ := Real.log (2 / 1)
  have hx171 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x171 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x172 : ℝ := c*c
  have hx172 : Bounds (1347110209 / 40000000000) (337934689 / 10000000000) x172 := by
    apply bounds_mul hc hc <;> norm_num
  let x173 : ℝ := -x172
  have hx173 : Bounds (-337934689 / 10000000000) (-1347110209 / 40000000000) x173 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx172
  let x174 : ℝ := (1 / 1)+x173
  have hx174 : Bounds (9662065311 / 10000000000) (38652889791 / 40000000000) x174 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx173 <;> norm_num
  let x175 : ℝ := (1 / 1)-x172
  have hx175 : Bounds (9662065311 / 10000000000) (38652889791 / 40000000000) x175 := by
    exact hx174
  let x176 : ℝ := Real.log x175
  have hx176 : Bounds (-8594417 / 250000000) (-34257913 / 1000000000) x176 := by
    exact bounds_log hx175 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (-8594417 / 500000000) (-34257913 / 2000000000) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (-8594417 / 500000000) (-34257913 / 2000000000) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (34257913 / 2000000000) (8594417 / 500000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x171+x180
  have hx181 : Bounds (1420552273 / 2000000000) (142067203 / 200000000) x181 := by
    apply bounds_add hx171 hx180 <;> norm_num
  let x182 : ℝ := x171-x179
  have hx182 : Bounds (1420552273 / 2000000000) (142067203 / 200000000) x182 := by
    exact hx181
  let x183 : ℝ := Real.log (2 / 1)
  have hx183 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x183 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x184 : ℝ := (1 / 1)+(18383 / 100000)
  have hx184 : Bounds (118383 / 100000) (118383 / 100000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((18383 / 100000) : ℝ)) <;> norm_num
  let x185 : ℝ := (1 / 1)+(18383 / 100000)
  have hx185 : Bounds (118383 / 100000) (118383 / 100000) x185 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((18383 / 100000) : ℝ)) <;> norm_num
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (33750989 / 200000000) (84377473 / 500000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x187 : ℝ := x184*x186
  have hx187 : Bounds (199777166539 / 1000000000000) (49944291931 / 250000000000) x187 := by
    apply bounds_mul hx184 hx186 <;> norm_num
  let x188 : ℝ := -(18383 / 100000)
  have hx188 : Bounds (-18383 / 100000) (-18383 / 100000) x188 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((18383 / 100000) : ℝ))
  let x189 : ℝ := (1 / 1)+x188
  have hx189 : Bounds (81617 / 100000) (81617 / 100000) x189 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx188 <;> norm_num
  let x190 : ℝ := (1 / 1)-(18383 / 100000)
  have hx190 : Bounds (81617 / 100000) (81617 / 100000) x190 := by
    exact hx189
  let x191 : ℝ := -(18383 / 100000)
  have hx191 : Bounds (-18383 / 100000) (-18383 / 100000) x191 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((18383 / 100000) : ℝ))
  let x192 : ℝ := (1 / 1)+x191
  have hx192 : Bounds (81617 / 100000) (81617 / 100000) x192 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx191 <;> norm_num
  let x193 : ℝ := (1 / 1)-(18383 / 100000)
  have hx193 : Bounds (81617 / 100000) (81617 / 100000) x193 := by
    exact hx192
  let x194 : ℝ := Real.log x193
  have hx194 : Bounds (-203132613 / 1000000000) (-50783153 / 250000000) x194 := by
    exact bounds_log hx193 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x195 : ℝ := x190*x194
  have hx195 : Bounds (-165790744753 / 1000000000000) (-1295240187 / 7812500000) x195 := by
    apply bounds_mul hx190 hx194 <;> norm_num
  let x196 : ℝ := x187+x195
  have hx196 : Bounds (16993210893 / 500000000000) (8496605947 / 250000000000) x196 := by
    apply bounds_add hx187 hx195 <;> norm_num
  let x197 : ℝ := (2 / 1)⁻¹
  have hx197 : Bounds (1 / 2) (1 / 2) x197 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x198 : ℝ := x196*x197
  have hx198 : Bounds (16993210893 / 1000000000000) (8496605947 / 500000000000) x198 := by
    apply bounds_mul hx196 hx197 <;> norm_num
  let x199 : ℝ := x196/(2 / 1)
  have hx199 : Bounds (16993210893 / 1000000000000) (8496605947 / 500000000000) x199 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx198
  let x200 : ℝ := -x199
  have hx200 : Bounds (-8496605947 / 500000000000) (-16993210893 / 1000000000000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx199
  let x201 : ℝ := x183+x200
  have hx201 : Bounds (338076984053 / 500000000000) (676153970107 / 1000000000000) x201 := by
    apply bounds_add hx183 hx200 <;> norm_num
  let x202 : ℝ := x183-x199
  have hx202 : Bounds (338076984053 / 500000000000) (676153970107 / 1000000000000) x202 := by
    exact hx201
  let x203 : ℝ := biasE (18383 / 100000)
  have hx203 : Bounds (338076984053 / 500000000000) (676153970107 / 1000000000000) x203 := by
    simpa +zetaDelta only [biasE, div_one] using hx202
  let x204 : ℝ := Real.log (2 / 1)
  have hx204 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x204 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x205 : ℝ := (1 / 1)+(36703 / 200000)
  have hx205 : Bounds (236703 / 200000) (236703 / 200000) x205 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((36703 / 200000) : ℝ)) <;> norm_num
  let x206 : ℝ := (1 / 1)+(36703 / 200000)
  have hx206 : Bounds (236703 / 200000) (236703 / 200000) x206 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((36703 / 200000) : ℝ)) <;> norm_num
  let x207 : ℝ := Real.log x206
  have hx207 : Bounds (21061103 / 125000000) (6739553 / 40000000) x207 := by
    exact bounds_log hx206 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x208 : ℝ := x205*x207
  have hx208 : Bounds (24926131317 / 125000000000) (4985226293 / 25000000000) x208 := by
    apply bounds_mul hx205 hx207 <;> norm_num
  let x209 : ℝ := -(36703 / 200000)
  have hx209 : Bounds (-36703 / 200000) (-36703 / 200000) x209 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((36703 / 200000) : ℝ))
  let x210 : ℝ := (1 / 1)+x209
  have hx210 : Bounds (163297 / 200000) (163297 / 200000) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx209 <;> norm_num
  let x211 : ℝ := (1 / 1)-(36703 / 200000)
  have hx211 : Bounds (163297 / 200000) (163297 / 200000) x211 := by
    exact hx210
  let x212 : ℝ := -(36703 / 200000)
  have hx212 : Bounds (-36703 / 200000) (-36703 / 200000) x212 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((36703 / 200000) : ℝ))
  let x213 : ℝ := (1 / 1)+x212
  have hx213 : Bounds (163297 / 200000) (163297 / 200000) x213 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx212 <;> norm_num
  let x214 : ℝ := (1 / 1)-(36703 / 200000)
  have hx214 : Bounds (163297 / 200000) (163297 / 200000) x214 := by
    exact hx213
  let x215 : ℝ := Real.log x214
  have hx215 : Bounds (-101373369 / 500000000) (-202746737 / 1000000000) x215 := by
    exact bounds_log hx214 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x216 : ℝ := x211*x215
  have hx216 : Bounds (-20692458797 / 125000000000) (-165539669559 / 1000000000000) x216 := by
    apply bounds_mul hx211 hx215 <;> norm_num
  let x217 : ℝ := x208+x216
  have hx217 : Bounds (105841813 / 3125000000) (33869382161 / 1000000000000) x217 := by
    apply bounds_add hx208 hx216 <;> norm_num
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (105841813 / 6250000000) (16934691081 / 1000000000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (105841813 / 6250000000) (16934691081 / 1000000000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := -x220
  have hx221 : Bounds (-16934691081 / 1000000000000) (-105841813 / 6250000000) x221 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx220
  let x222 : ℝ := x204+x221
  have hx222 : Bounds (676212488919 / 1000000000000) (16905312273 / 25000000000) x222 := by
    apply bounds_add hx204 hx221 <;> norm_num
  let x223 : ℝ := x204-x220
  have hx223 : Bounds (676212488919 / 1000000000000) (16905312273 / 25000000000) x223 := by
    exact hx222
  let x224 : ℝ := biasE (36703 / 200000)
  have hx224 : Bounds (676212488919 / 1000000000000) (16905312273 / 25000000000) x224 := by
    simpa +zetaDelta only [biasE, div_one] using hx223
  let x225 : ℝ := biasE c
  have hx225 : Bounds (338076984053 / 500000000000) (16905312273 / 25000000000) x225 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx203.1 hx224.2
  let x226 : ℝ := x159⁻¹
  have hx226 : Bounds (3830611104763 / 1000000000000) (3837261494437 / 1000000000000) x226 := by
    apply bounds_inv hx159 <;> norm_num
  let x227 : ℝ := x148*x226
  have hx227 : Bounds (35916488311 / 25000000000) (1441734133143 / 1000000000000) x227 := by
    apply bounds_mul hx148 hx226 <;> norm_num
  let x228 : ℝ := x148/x159
  have hx228 : Bounds (35916488311 / 25000000000) (1441734133143 / 1000000000000) x228 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx227
  let x229 : ℝ := c*x148
  have hx229 : Bounds (68826765987 / 1000000000000) (34534261749 / 500000000000) x229 := by
    apply bounds_mul hc hx148 <;> norm_num
  let x230 : ℝ := x225+x229
  have hx230 : Bounds (744980734093 / 1000000000000) (372640507209 / 500000000000) x230 := by
    apply bounds_add hx225 hx229 <;> norm_num
  let x231 : ℝ := x*x170
  have hx231 : Bounds (33262561251 / 1000000000000) (6675091129 / 200000000000) x231 := by
    apply bounds_mul hx hx170 <;> norm_num
  let x232 : ℝ := x48+x231
  have hx232 : Bounds (69346197077 / 100000000000) (693684842161 / 1000000000000) x232 := by
    apply bounds_add hx48 hx231 <;> norm_num
  let x233 : ℝ := x232⁻¹
  have hx233 : Bounds (1441576836081 / 1000000000000) (144204014373 / 100000000000) x233 := by
    apply bounds_inv hx232 <;> norm_num
  let x234 : ℝ := x230*x233
  have hx234 : Bounds (214789393919 / 200000000000) (1074725141151 / 1000000000000) x234 := by
    apply bounds_mul hx230 hx233 <;> norm_num
  let x235 : ℝ := x230/x232
  have hx235 : Bounds (214789393919 / 200000000000) (1074725141151 / 1000000000000) x235 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx234
  let x236 : ℝ := y*y
  have hx236 : Bounds (64953109881 / 1000000000000) (16292224881 / 250000000000) x236 := by
    apply bounds_mul hy hy <;> norm_num
  let x237 : ℝ := -x236
  have hx237 : Bounds (-16292224881 / 250000000000) (-64953109881 / 1000000000000) x237 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx236
  let x238 : ℝ := (1 / 1)+x237
  have hx238 : Bounds (233707775119 / 250000000000) (935046890119 / 1000000000000) x238 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx237 <;> norm_num
  let x239 : ℝ := (1 / 1)-x236
  have hx239 : Bounds (233707775119 / 250000000000) (935046890119 / 1000000000000) x239 := by
    exact hx238
  let x240 : ℝ := x239*x159
  have hx240 : Bounds (243619336819 / 1000000000000) (122049310743 / 500000000000) x240 := by
    apply bounds_mul hx239 hx159 <;> norm_num
  let x241 : ℝ := c*c
  have hx241 : Bounds (1347110209 / 40000000000) (337934689 / 10000000000) x241 := by
    apply bounds_mul hc hc <;> norm_num
  let x242 : ℝ := -x241
  have hx242 : Bounds (-337934689 / 10000000000) (-1347110209 / 40000000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx241
  let x243 : ℝ := (1 / 1)+x242
  have hx243 : Bounds (9662065311 / 10000000000) (38652889791 / 40000000000) x243 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx242 <;> norm_num
  let x244 : ℝ := (1 / 1)-x241
  have hx244 : Bounds (9662065311 / 10000000000) (38652889791 / 40000000000) x244 := by
    exact hx243
  let x245 : ℝ := x244*x182
  have hx245 : Bounds (68627344197 / 100000000000) (8580168657 / 12500000000) x245 := by
    apply bounds_mul hx244 hx182 <;> norm_num
  let x246 : ℝ := y*y
  have hx246 : Bounds (64953109881 / 1000000000000) (16292224881 / 250000000000) x246 := by
    apply bounds_mul hy hy <;> norm_num
  let x247 : ℝ := (1 / 1)+x246
  have hx247 : Bounds (1064953109881 / 1000000000000) (266292224881 / 250000000000) x247 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx246 <;> norm_num
  let x248 : ℝ := x247*x159
  have hx248 : Bounds (277529459857 / 1000000000000) (27806761647 / 100000000000) x248 := by
    apply bounds_mul hx247 hx159 <;> norm_num
  let x249 : ℝ := -y
  have hx249 : Bounds (-127641 / 500000) (-254859 / 1000000) x249 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x250 : ℝ := x248+x249
  have hx250 : Bounds (22247459857 / 1000000000000) (2320861647 / 100000000000) x250 := by
    apply bounds_add hx248 hx249 <;> norm_num
  let x251 : ℝ := x248-y
  have hx251 : Bounds (22247459857 / 1000000000000) (2320861647 / 100000000000) x251 := by
    exact hx250
  let x252 : ℝ := x240*x240
  have hx252 : Bounds (7418797659 / 125000000000) (14896034253 / 250000000000) x252 := by
    apply bounds_mul hx240 hx240 <;> norm_num
  let x253 : ℝ := x252⁻¹
  have hx253 : Bounds (2097873801123 / 125000000000) (2106136427787 / 125000000000) x253 := by
    apply bounds_inv hx252 <;> norm_num
  let x254 : ℝ := x251*x253
  have hx254 : Bounds (93344726351 / 250000000000) (391044100689 / 1000000000000) x254 := by
    apply bounds_mul hx251 hx253 <;> norm_num
  let x255 : ℝ := x251/x252
  have hx255 : Bounds (93344726351 / 250000000000) (391044100689 / 1000000000000) x255 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx254
  let x256 : ℝ := (-2 / 1)*x255
  have hx256 : Bounds (-391044100689 / 500000000000) (-93344726351 / 125000000000) x256 := by
    apply bounds_mul (bounds_const ((-2 / 1) : ℝ)) hx255 <;> norm_num
  let x257 : ℝ := x256*x228
  have hx257 : Bounds (-70472703441 / 62500000000) (-1072836727321 / 1000000000000) x257 := by
    apply bounds_mul hx256 hx228 <;> norm_num
  let x258 : ℝ := (2 / 1)*x182
  have hx258 : Bounds (1420552273 / 1000000000) (142067203 / 100000000) x258 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx182 <;> norm_num
  let x259 : ℝ := c*c
  have hx259 : Bounds (1347110209 / 40000000000) (337934689 / 10000000000) x259 := by
    apply bounds_mul hc hc <;> norm_num
  let x260 : ℝ := -x259
  have hx260 : Bounds (-337934689 / 10000000000) (-1347110209 / 40000000000) x260 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx259
  let x261 : ℝ := x258+x260
  have hx261 : Bounds (13867588041 / 10000000000) (55479770991 / 40000000000) x261 := by
    apply bounds_add hx258 hx260 <;> norm_num
  let x262 : ℝ := x258-x259
  have hx262 : Bounds (13867588041 / 10000000000) (55479770991 / 40000000000) x262 := by
    exact hx261
  let x263 : ℝ := c*x262
  have hx263 : Bounds (127245520967 / 500000000000) (63742789383 / 250000000000) x263 := by
    apply bounds_mul hc hx262 <;> norm_num
  let x264 : ℝ := x245*x245
  have hx264 : Bounds (470971237153 / 1000000000000) (471163482769 / 1000000000000) x264 := by
    apply bounds_mul hx245 hx245 <;> norm_num
  let x265 : ℝ := x264⁻¹
  have hx265 : Bounds (424481113911 / 200000000000) (424654382737 / 200000000000) x265 := by
    apply bounds_inv hx264 <;> norm_num
  let x266 : ℝ := x263*x265
  have hx266 : Bounds (270066602401 / 500000000000) (135343274397 / 250000000000) x266 := by
    apply bounds_mul hx263 hx265 <;> norm_num
  let x267 : ℝ := x263/x264
  have hx267 : Bounds (270066602401 / 500000000000) (135343274397 / 250000000000) x267 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx266
  let x268 : ℝ := (2 / 1)*x267
  have hx268 : Bounds (270066602401 / 250000000000) (135343274397 / 125000000000) x268 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx267 <;> norm_num
  let x269 : ℝ := x268*x235
  have hx269 : Bounds (1160148836949 / 1000000000000) (581827278721 / 500000000000) x269 := by
    apply bounds_mul hx268 hx235 <;> norm_num
  let x270 : ℝ := x257+x269
  have hx270 : Bounds (32585581893 / 1000000000000) (90817830121 / 1000000000000) x270 := by
    apply bounds_add hx257 hx269 <;> norm_num
  have hPos : 0 < x270 :=
    lt_of_lt_of_le (by norm_num) hx270.1
  have hBridgeL : doubleCapBridgeL x = x48 := by
    exact hEll'
  rw [← doubleCapBridgeDerivativeTraceForm_eq x]
  simpa +zetaDelta only [doubleCapBridgeDerivativeTraceForm,
    hBridgeL, SmallMean.A, biasB, div_one, pow_two] using hPos

theorem acceptedCell : DoubleCapBridgeDerivativeCellCertificate
    (⟨185, by decide⟩ : Fin 256) doubleCapBridgeDerivativeExpression where
  positive x hx := by
    have hloEq : doubleCapBridgeLo (⟨185, by decide⟩ : Fin 256) =
        (367 / 2048) := by norm_num [doubleCapBridgeLo, doubleCapBridgeStep]
    have hhiEq : doubleCapBridgeHi (⟨185, by decide⟩ : Fin 256) =
        (919 / 5120) := by norm_num [doubleCapBridgeHi, doubleCapBridgeStep]
    have hlo : (367 / 2048) ≤ x := by
      simpa only [hloEq] using hx.1
    have hhi : x ≤ (919 / 5120) := by
      simpa only [hhiEq] using hx.2
    exact cell_derivative_pos x ⟨hlo, hhi⟩

#print axioms cell_derivative_pos
#print axioms acceptedCell

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell185

end


