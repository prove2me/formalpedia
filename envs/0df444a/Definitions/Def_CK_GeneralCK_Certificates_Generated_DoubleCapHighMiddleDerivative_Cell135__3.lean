-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell135__3
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell135__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T14:55:53.348001+00:00
-- url     : https://prove2.me/theorems/4b1a520f-59dd-489e-ba5e-ada42f3369dd
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell135 (+2 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell136, Ge…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell135 (+2 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell136, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell137)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell135 (+2 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell136, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell137)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell135 (+2 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell136, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell137) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell135 (+2 modules: GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell136, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell137).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapHighMiddleDerivativeTraceForm
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell131Logs__7

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell135 =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell135
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_derivative_pos (x : ℝ)
    (hx : Bounds (337 / 2048) (211 / 1280) x) :
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
  have hx0 : Bounds (337 / 1024) (211 / 640) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx <;> norm_num
  let x1 : ℝ := Real.log (2 / 1)
  have hx1 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x1 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x2 : ℝ := Real.log (2 / 1)
  have hx2 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x2 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x3 : ℝ := (1 / 1)+(211 / 640)
  have hx3 : Bounds (851 / 640) (851 / 640) x3 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((211 / 640) : ℝ)) <;> norm_num
  let x4 : ℝ := (1 / 1)+(211 / 640)
  have hx4 : Bounds (851 / 640) (851 / 640) x4 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((211 / 640) : ℝ)) <;> norm_num
  let x5 : ℝ := Real.log x4
  have hx5 : Bounds (17808997 / 62500000) (284943953 / 1000000000) x5 := by
    exact bounds_log hx4 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x6 : ℝ := x3*x5
  have hx6 : Bounds (15155456447 / 40000000000) (75777282501 / 200000000000) x6 := by
    apply bounds_mul hx3 hx5 <;> norm_num
  let x7 : ℝ := -(211 / 640)
  have hx7 : Bounds (-211 / 640) (-211 / 640) x7 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((211 / 640) : ℝ))
  let x8 : ℝ := (1 / 1)+x7
  have hx8 : Bounds (429 / 640) (429 / 640) x8 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx7 <;> norm_num
  let x9 : ℝ := (1 / 1)-(211 / 640)
  have hx9 : Bounds (429 / 640) (429 / 640) x9 := by
    exact hx8
  let x10 : ℝ := -(211 / 640)
  have hx10 : Bounds (-211 / 640) (-211 / 640) x10 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((211 / 640) : ℝ))
  let x11 : ℝ := (1 / 1)+x10
  have hx11 : Bounds (429 / 640) (429 / 640) x11 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx10 <;> norm_num
  let x12 : ℝ := (1 / 1)-(211 / 640)
  have hx12 : Bounds (429 / 640) (429 / 640) x12 := by
    exact hx11
  let x13 : ℝ := Real.log x12
  have hx13 : Bounds (-200005629 / 500000000) (-400011257 / 1000000000) x13 := by
    exact bounds_log hx12 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x14 : ℝ := x9*x13
  have hx14 : Bounds (-268132546379 / 1000000000000) (-268132545707 / 1000000000000) x14 := by
    apply bounds_mul hx9 hx13 <;> norm_num
  let x15 : ℝ := x6+x14
  have hx15 : Bounds (27688466199 / 250000000000) (55376933399 / 500000000000) x15 := by
    apply bounds_add hx6 hx14 <;> norm_num
  let x16 : ℝ := (2 / 1)⁻¹
  have hx16 : Bounds (1 / 2) (1 / 2) x16 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x17 : ℝ := x15*x16
  have hx17 : Bounds (27688466199 / 500000000000) (55376933399 / 1000000000000) x17 := by
    apply bounds_mul hx15 hx16 <;> norm_num
  let x18 : ℝ := x15/(2 / 1)
  have hx18 : Bounds (27688466199 / 500000000000) (55376933399 / 1000000000000) x18 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx17
  let x19 : ℝ := -x18
  have hx19 : Bounds (-55376933399 / 1000000000000) (-27688466199 / 500000000000) x19 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx18
  let x20 : ℝ := x2+x19
  have hx20 : Bounds (637770246601 / 1000000000000) (318885124301 / 500000000000) x20 := by
    apply bounds_add hx2 hx19 <;> norm_num
  let x21 : ℝ := x2-x18
  have hx21 : Bounds (637770246601 / 1000000000000) (318885124301 / 500000000000) x21 := by
    exact hx20
  let x22 : ℝ := biasE (211 / 640)
  have hx22 : Bounds (637770246601 / 1000000000000) (318885124301 / 500000000000) x22 := by
    simpa +zetaDelta only [biasE, div_one] using hx21
  let x23 : ℝ := Real.log (2 / 1)
  have hx23 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x23 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x24 : ℝ := (1 / 1)+(337 / 1024)
  have hx24 : Bounds (1361 / 1024) (1361 / 1024) x24 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((337 / 1024) : ℝ)) <;> norm_num
  let x25 : ℝ := (1 / 1)+(337 / 1024)
  have hx25 : Bounds (1361 / 1024) (1361 / 1024) x25 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((337 / 1024) : ℝ)) <;> norm_num
  let x26 : ℝ := Real.log x25
  have hx26 : Bounds (284503197 / 1000000000) (142251599 / 500000000) x26 := by
    exact bounds_log hx25 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x27 : ℝ := x24*x26
  have hx27 : Bounds (94533410917 / 250000000000) (378133644999 / 1000000000000) x27 := by
    apply bounds_mul hx24 hx26 <;> norm_num
  let x28 : ℝ := -(337 / 1024)
  have hx28 : Bounds (-337 / 1024) (-337 / 1024) x28 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((337 / 1024) : ℝ))
  let x29 : ℝ := (1 / 1)+x28
  have hx29 : Bounds (687 / 1024) (687 / 1024) x29 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx28 <;> norm_num
  let x30 : ℝ := (1 / 1)-(337 / 1024)
  have hx30 : Bounds (687 / 1024) (687 / 1024) x30 := by
    exact hx29
  let x31 : ℝ := -(337 / 1024)
  have hx31 : Bounds (-337 / 1024) (-337 / 1024) x31 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((337 / 1024) : ℝ))
  let x32 : ℝ := (1 / 1)+x31
  have hx32 : Bounds (687 / 1024) (687 / 1024) x32 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx31 <;> norm_num
  let x33 : ℝ := (1 / 1)-(337 / 1024)
  have hx33 : Bounds (687 / 1024) (687 / 1024) x33 := by
    exact hx32
  let x34 : ℝ := Real.log x33
  have hx34 : Bounds (-199568757 / 500000000) (-399137513 / 1000000000) x34 := by
    exact bounds_log hx33 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x35 : ℝ := x30*x34
  have hx35 : Bounds (-267780734491 / 1000000000000) (-267780733819 / 1000000000000) x35 := by
    apply bounds_mul hx30 hx34 <;> norm_num
  let x36 : ℝ := x27+x35
  have hx36 : Bounds (110352909177 / 1000000000000) (5517645559 / 50000000000) x36 := by
    apply bounds_add hx27 hx35 <;> norm_num
  let x37 : ℝ := (2 / 1)⁻¹
  have hx37 : Bounds (1 / 2) (1 / 2) x37 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x38 : ℝ := x36*x37
  have hx38 : Bounds (13794113647 / 250000000000) (5517645559 / 100000000000) x38 := by
    apply bounds_mul hx36 hx37 <;> norm_num
  let x39 : ℝ := x36/(2 / 1)
  have hx39 : Bounds (13794113647 / 250000000000) (5517645559 / 100000000000) x39 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx38
  let x40 : ℝ := -x39
  have hx40 : Bounds (-5517645559 / 100000000000) (-13794113647 / 250000000000) x40 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx39
  let x41 : ℝ := x23+x40
  have hx41 : Bounds (63797072441 / 100000000000) (159492681603 / 250000000000) x41 := by
    apply bounds_add hx23 hx40 <;> norm_num
  let x42 : ℝ := x23-x39
  have hx42 : Bounds (63797072441 / 100000000000) (159492681603 / 250000000000) x42 := by
    exact hx41
  let x43 : ℝ := biasE (337 / 1024)
  have hx43 : Bounds (63797072441 / 100000000000) (159492681603 / 250000000000) x43 := by
    simpa +zetaDelta only [biasE, div_one] using hx42
  let x44 : ℝ := biasE x0
  have hx44 : Bounds (637770246601 / 1000000000000) (159492681603 / 250000000000) x44 := by
    exact bounds_biasE hx0 (by norm_num) (by norm_num) hx22.1 hx43.2
  let x45 : ℝ := x1+x44
  have hx45 : Bounds (1330917426601 / 1000000000000) (332779476853 / 250000000000) x45 := by
    apply bounds_add hx1 hx44 <;> norm_num
  let x46 : ℝ := (2 / 1)⁻¹
  have hx46 : Bounds (1 / 2) (1 / 2) x46 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x47 : ℝ := x45*x46
  have hx47 : Bounds (6654587133 / 10000000000) (332779476853 / 500000000000) x47 := by
    apply bounds_mul hx45 hx46 <;> norm_num
  let x48 : ℝ := x45/(2 / 1)
  have hx48 : Bounds (6654587133 / 10000000000) (332779476853 / 500000000000) x48 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx47
  let x49 : ℝ := Real.log (2 / 1)
  have hx49 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x49 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x50 : ℝ := (1 / 1)+(233809 / 1000000)
  have hx50 : Bounds (1233809 / 1000000) (1233809 / 1000000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((233809 / 1000000) : ℝ)) <;> norm_num
  let x51 : ℝ := (1 / 1)+(233809 / 1000000)
  have hx51 : Bounds (1233809 / 1000000) (1233809 / 1000000) x51 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((233809 / 1000000) : ℝ)) <;> norm_num
  let x52 : ℝ := Real.log x51
  have hx52 : Bounds (52526533 / 250000000) (210106133 / 1000000000) x52 := by
    exact bounds_log hx51 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x53 : ℝ := x50*x52
  have hx53 : Bounds (32403854577 / 125000000000) (259230837851 / 1000000000000) x53 := by
    apply bounds_mul hx50 hx52 <;> norm_num
  let x54 : ℝ := -(233809 / 1000000)
  have hx54 : Bounds (-233809 / 1000000) (-233809 / 1000000) x54 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((233809 / 1000000) : ℝ))
  let x55 : ℝ := (1 / 1)+x54
  have hx55 : Bounds (766191 / 1000000) (766191 / 1000000) x55 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx54 <;> norm_num
  let x56 : ℝ := (1 / 1)-(233809 / 1000000)
  have hx56 : Bounds (766191 / 1000000) (766191 / 1000000) x56 := by
    exact hx55
  let x57 : ℝ := -(233809 / 1000000)
  have hx57 : Bounds (-233809 / 1000000) (-233809 / 1000000) x57 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((233809 / 1000000) : ℝ))
  let x58 : ℝ := (1 / 1)+x57
  have hx58 : Bounds (766191 / 1000000) (766191 / 1000000) x58 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx57 <;> norm_num
  let x59 : ℝ := (1 / 1)-(233809 / 1000000)
  have hx59 : Bounds (766191 / 1000000) (766191 / 1000000) x59 := by
    exact hx58
  let x60 : ℝ := Real.log x59
  have hx60 : Bounds (-133161897 / 500000000) (-266323793 / 1000000000) x60 := by
    exact bounds_log hx59 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x61 : ℝ := x56*x60
  have hx61 : Bounds (-204054894049 / 1000000000000) (-102027446641 / 500000000000) x61 := by
    apply bounds_mul hx56 hx60 <;> norm_num
  let x62 : ℝ := x53+x61
  have hx62 : Bounds (55175942567 / 1000000000000) (55175944569 / 1000000000000) x62 := by
    apply bounds_add hx53 hx61 <;> norm_num
  let x63 : ℝ := (2 / 1)⁻¹
  have hx63 : Bounds (1 / 2) (1 / 2) x63 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x64 : ℝ := x62*x63
  have hx64 : Bounds (27587971283 / 1000000000000) (5517594457 / 200000000000) x64 := by
    apply bounds_mul hx62 hx63 <;> norm_num
  let x65 : ℝ := x62/(2 / 1)
  have hx65 : Bounds (27587971283 / 1000000000000) (5517594457 / 200000000000) x65 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx64
  let x66 : ℝ := -x65
  have hx66 : Bounds (-5517594457 / 200000000000) (-27587971283 / 1000000000000) x66 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx65
  let x67 : ℝ := x49+x66
  have hx67 : Bounds (133111841543 / 200000000000) (665559209717 / 1000000000000) x67 := by
    apply bounds_add hx49 hx66 <;> norm_num
  let x68 : ℝ := x49-x65
  have hx68 : Bounds (133111841543 / 200000000000) (665559209717 / 1000000000000) x68 := by
    exact hx67
  let x69 : ℝ := biasE (233809 / 1000000)
  have hx69 : Bounds (133111841543 / 200000000000) (665559209717 / 1000000000000) x69 := by
    simpa +zetaDelta only [biasE, div_one] using hx68
  let x70 : ℝ := Real.log (2 / 1)
  have hx70 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x70 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x71 : ℝ := (1 / 1)+(234231 / 1000000)
  have hx71 : Bounds (1234231 / 1000000) (1234231 / 1000000) x71 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((234231 / 1000000) : ℝ)) <;> norm_num
  let x72 : ℝ := (1 / 1)+(234231 / 1000000)
  have hx72 : Bounds (1234231 / 1000000) (1234231 / 1000000) x72 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((234231 / 1000000) : ℝ)) <;> norm_num
  let x73 : ℝ := Real.log x72
  have hx73 : Bounds (26306013 / 125000000) (42089621 / 200000000) x73 := by
    exact bounds_log hx72 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x74 : ℝ := x71*x73
  have hx74 : Bounds (32467696731 / 125000000000) (259741575083 / 1000000000000) x74 := by
    apply bounds_mul hx71 hx73 <;> norm_num
  let x75 : ℝ := -(234231 / 1000000)
  have hx75 : Bounds (-234231 / 1000000) (-234231 / 1000000) x75 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((234231 / 1000000) : ℝ))
  let x76 : ℝ := (1 / 1)+x75
  have hx76 : Bounds (765769 / 1000000) (765769 / 1000000) x76 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx75 <;> norm_num
  let x77 : ℝ := (1 / 1)-(234231 / 1000000)
  have hx77 : Bounds (765769 / 1000000) (765769 / 1000000) x77 := by
    exact hx76
  let x78 : ℝ := -(234231 / 1000000)
  have hx78 : Bounds (-234231 / 1000000) (-234231 / 1000000) x78 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((234231 / 1000000) : ℝ))
  let x79 : ℝ := (1 / 1)+x78
  have hx79 : Bounds (765769 / 1000000) (765769 / 1000000) x79 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx78 <;> norm_num
  let x80 : ℝ := (1 / 1)-(234231 / 1000000)
  have hx80 : Bounds (765769 / 1000000) (765769 / 1000000) x80 := by
    exact hx79
  let x81 : ℝ := Real.log x80
  have hx81 : Bounds (-133437361 / 500000000) (-266874721 / 1000000000) x81 := by
    exact bounds_log hx80 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x82 : ℝ := x77*x81
  have hx82 : Bounds (-1596596789 / 7812500000) (-8174575529 / 40000000000) x82 := by
    apply bounds_mul hx77 hx81 <;> norm_num
  let x83 : ℝ := x74+x82
  have hx83 : Bounds (6922148107 / 125000000000) (27688593429 / 500000000000) x83 := by
    apply bounds_add hx74 hx82 <;> norm_num
  let x84 : ℝ := (2 / 1)⁻¹
  have hx84 : Bounds (1 / 2) (1 / 2) x84 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x85 : ℝ := x83*x84
  have hx85 : Bounds (6922148107 / 250000000000) (27688593429 / 1000000000000) x85 := by
    apply bounds_mul hx83 hx84 <;> norm_num
  let x86 : ℝ := x83/(2 / 1)
  have hx86 : Bounds (6922148107 / 250000000000) (27688593429 / 1000000000000) x86 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx85
  let x87 : ℝ := -x86
  have hx87 : Bounds (-27688593429 / 1000000000000) (-6922148107 / 250000000000) x87 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx86
  let x88 : ℝ := x70+x87
  have hx88 : Bounds (665458586571 / 1000000000000) (166364647143 / 250000000000) x88 := by
    apply bounds_add hx70 hx87 <;> norm_num
  let x89 : ℝ := x70-x86
  have hx89 : Bounds (665458586571 / 1000000000000) (166364647143 / 250000000000) x89 := by
    exact hx88
  let x90 : ℝ := biasE (234231 / 1000000)
  have hx90 : Bounds (665458586571 / 1000000000000) (166364647143 / 250000000000) x90 := by
    simpa +zetaDelta only [biasE, div_one] using hx89
  let y : ℝ := doubleCapHighTailY x
  have hEll' : Real.log 2 * doubleCapHighTailFloor x = x48 := by
    simpa +zetaDelta only [div_one] using hEll
  have hy : Bounds (233809 / 1000000) (234231 / 1000000) y := by
    dsimp only [y, doubleCapHighTailY]
    apply entropyInverseBias_bracket hh0.le hh1.le
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (234231 / 1000000) ≤ (166364647143 / 250000000000) := hx90.2
      have h2 : (6654587133 / 10000000000) ≤ x48 := hx48.1
      linarith [hEll']
    · have h1 : x48 ≤ (332779476853 / 500000000000) := hx48.2
      have h2 : (133111841543 / 200000000000) ≤ biasE (233809 / 1000000) := hx69.1
      linarith [hEll']
  let x91 : ℝ := x⁻¹
  have hx91 : Bounds (60663507109 / 10000000000) (379821958457 / 62500000000) x91 := by
    apply bounds_inv hx <;> norm_num
  let x92 : ℝ := x48*x91
  have hx92 : Bounds (2018452969251 / 500000000000) (1011175621061 / 250000000000) x92 := by
    apply bounds_mul hx48 hx91 <;> norm_num
  let x93 : ℝ := x48/x
  have hx93 : Bounds (2018452969251 / 500000000000) (1011175621061 / 250000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(167871 / 1000000)
  have hx95 : Bounds (1167871 / 1000000) (1167871 / 1000000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((167871 / 1000000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(167871 / 1000000)
  have hx96 : Bounds (1167871 / 1000000) (1167871 / 1000000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((167871 / 1000000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (155182433 / 1000000000) (77591217 / 500000000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (18123306321 / 100000000000) (181233064379 / 1000000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(167871 / 1000000)
  have hx99 : Bounds (-167871 / 1000000) (-167871 / 1000000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((167871 / 1000000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (832129 / 1000000) (832129 / 1000000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(167871 / 1000000)
  have hx101 : Bounds (832129 / 1000000) (832129 / 1000000) x101 := by
    exact hx100
  let x102 : ℝ := -(167871 / 1000000)
  have hx102 : Bounds (-167871 / 1000000) (-167871 / 1000000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((167871 / 1000000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (832129 / 1000000) (832129 / 1000000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(167871 / 1000000)
  have hx104 : Bounds (832129 / 1000000) (832129 / 1000000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-183767803 / 1000000000) (-91883901 / 500000000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-152918518143 / 1000000000000) (-15291851731 / 100000000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (28314545067 / 1000000000000) (28314547069 / 1000000000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (14157272533 / 1000000000000) (2831454707 / 200000000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (14157272533 / 1000000000000) (2831454707 / 200000000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-2831454707 / 200000000000) (-14157272533 / 1000000000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (135797981293 / 200000000000) (678989908467 / 1000000000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (135797981293 / 200000000000) (678989908467 / 1000000000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (167871 / 1000000)
  have hx114 : Bounds (135797981293 / 200000000000) (678989908467 / 1000000000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(168183 / 1000000)
  have hx116 : Bounds (1168183 / 1000000) (1168183 / 1000000) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((168183 / 1000000) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(168183 / 1000000)
  have hx117 : Bounds (1168183 / 1000000) (1168183 / 1000000) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((168183 / 1000000) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (3108991 / 20000000) (155449551 / 1000000000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (181593521667 / 1000000000000) (45398380709 / 250000000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(168183 / 1000000)
  have hx120 : Bounds (-168183 / 1000000) (-168183 / 1000000) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((168183 / 1000000) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (831817 / 1000000) (831817 / 1000000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(168183 / 1000000)
  have hx122 : Bounds (831817 / 1000000) (831817 / 1000000) x122 := by
    exact hx121
  let x123 : ℝ := -(168183 / 1000000)
  have hx123 : Bounds (-168183 / 1000000) (-168183 / 1000000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((168183 / 1000000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (831817 / 1000000) (831817 / 1000000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(168183 / 1000000)
  have hx125 : Bounds (831817 / 1000000) (831817 / 1000000) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-36828563 / 200000000) (-92071407 / 500000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-30634624789 / 200000000000) (-153173123113 / 1000000000000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (14210198861 / 500000000000) (28420399723 / 1000000000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (14210198861 / 1000000000000) (7105099931 / 500000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (14210198861 / 1000000000000) (7105099931 / 500000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-7105099931 / 500000000000) (-14210198861 / 1000000000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (339468490069 / 500000000000) (678936982139 / 1000000000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (339468490069 / 500000000000) (678936982139 / 1000000000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (168183 / 1000000)
  have hx135 : Bounds (339468490069 / 500000000000) (678936982139 / 1000000000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(167871 / 1000000)
  have hx136 : Bounds (338839718401 / 500000000000) (678988250733 / 1000000000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((167871 / 1000000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(168183 / 1000000)
  have hx137 : Bounds (135787790291 / 200000000000) (170062549477 / 250000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((168183 / 1000000) : ℝ)) <;> norm_num
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
  have hc : Bounds (167871 / 1000000) (168183 / 1000000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num)
      (by norm_num) (show 0 < x93 by linarith [hx93.1]) hcEq
    · have h1 : x93 * (167871 / 1000000) ≤ (678988250733 / 1000000000000) := hx136.2
      have h2 : (135797981293 / 200000000000) ≤ biasE (167871 / 1000000) := hx114.1
      linarith
    · have h1 : biasE (168183 / 1000000) ≤ (678936982139 / 1000000000000) := hx135.2
      have h2 : (135787790291 / 200000000000) ≤ x93 * (168183 / 1000000) := hx137.1
      linarith
  let x138 : ℝ := (1 / 1)+x0
  have hx138 : Bounds (1361 / 1024) (851 / 640) x138 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx0 <;> norm_num
  let x139 : ℝ := -x0
  have hx139 : Bounds (-211 / 640) (-337 / 1024) x139 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x140 : ℝ := (1 / 1)+x139
  have hx140 : Bounds (429 / 640) (687 / 1024) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx139 <;> norm_num
  let x141 : ℝ := (1 / 1)-x0
  have hx141 : Bounds (429 / 640) (687 / 1024) x141 := by
    exact hx140
  let x142 : ℝ := x141⁻¹
  have hx142 : Bounds (372634643377 / 250000000000) (745920745921 / 500000000000) x142 := by
    apply bounds_inv hx141 <;> norm_num
  let x143 : ℝ := x138*x142
  have hx143 : Bounds (247634643377 / 125000000000) (495920745921 / 250000000000) x143 := by
    apply bounds_mul hx138 hx142 <;> norm_num
  let x144 : ℝ := x138/x141
  have hx144 : Bounds (247634643377 / 125000000000) (495920745921 / 250000000000) x144 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx143
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (68364071 / 100000000) (68495521 / 100000000) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_14.2)
  let x146 : ℝ := (2 / 1)⁻¹
  have hx146 : Bounds (1 / 2) (1 / 2) x146 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x147 : ℝ := x145*x146
  have hx147 : Bounds (68364071 / 200000000) (68495521 / 200000000) x147 := by
    apply bounds_mul hx145 hx146 <;> norm_num
  let x148 : ℝ := x145/(2 / 1)
  have hx148 : Bounds (68364071 / 200000000) (68495521 / 200000000) x148 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx147
  let x149 : ℝ := (1 / 1)+y
  have hx149 : Bounds (1233809 / 1000000) (1234231 / 1000000) x149 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x150 : ℝ := -y
  have hx150 : Bounds (-234231 / 1000000) (-233809 / 1000000) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (765769 / 1000000) (766191 / 1000000) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-y
  have hx152 : Bounds (765769 / 1000000) (766191 / 1000000) x152 := by
    exact hx151
  let x153 : ℝ := x152⁻¹
  have hx153 : Bounds (1305157591253 / 1000000000000) (326469209383 / 250000000000) x153 := by
    apply bounds_inv hx152 <;> norm_num
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (805157591253 / 500000000000) (201469209383 / 125000000000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x149/x152
  have hx155 : Bounds (805157591253 / 500000000000) (201469209383 / 125000000000) x155 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx154
  let x156 : ℝ := Real.log x155
  have hx156 : Bounds (19057197 / 40000000) (238661413 / 500000000) x156 := by
    exact bounds_log hx155 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_16.2)
  let x157 : ℝ := (2 / 1)⁻¹
  have hx157 : Bounds (1 / 2) (1 / 2) x157 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x158 : ℝ := x156*x157
  have hx158 : Bounds (19057197 / 80000000) (238661413 / 1000000000) x158 := by
    apply bounds_mul hx156 hx157 <;> norm_num
  let x159 : ℝ := x156/(2 / 1)
  have hx159 : Bounds (19057197 / 80000000) (238661413 / 1000000000) x159 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx158
  let x160 : ℝ := (1 / 1)+c
  have hx160 : Bounds (1167871 / 1000000) (1168183 / 1000000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x161 : ℝ := -c
  have hx161 : Bounds (-168183 / 1000000) (-167871 / 1000000) x161 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x162 : ℝ := (1 / 1)+x161
  have hx162 : Bounds (831817 / 1000000) (832129 / 1000000) x162 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx161 <;> norm_num
  let x163 : ℝ := (1 / 1)-c
  have hx163 : Bounds (831817 / 1000000) (832129 / 1000000) x163 := by
    exact hx162
  let x164 : ℝ := x163⁻¹
  have hx164 : Bounds (1201736749951 / 1000000000000) (150273437547 / 125000000000) x164 := by
    apply bounds_inv hx163 <;> norm_num
  let x165 : ℝ := x160*x164
  have hx165 : Bounds (701736749951 / 500000000000) (87773437547 / 62500000000) x165 := by
    apply bounds_mul hx160 hx164 <;> norm_num
  let x166 : ℝ := x160/x163
  have hx166 : Bounds (701736749951 / 500000000000) (87773437547 / 62500000000) x166 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx165
  let x167 : ℝ := Real.log x166
  have hx167 : Bounds (67790047 / 200000000) (67918473 / 200000000) x167 := by
    exact bounds_log hx166 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x168 : ℝ := (2 / 1)⁻¹
  have hx168 : Bounds (1 / 2) (1 / 2) x168 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x169 : ℝ := x167*x168
  have hx169 : Bounds (67790047 / 400000000) (67918473 / 400000000) x169 := by
    apply bounds_mul hx167 hx168 <;> norm_num
  let x170 : ℝ := x167/(2 / 1)
  have hx170 : Bounds (67790047 / 400000000) (67918473 / 400000000) x170 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx169
  let x171 : ℝ := Real.log (2 / 1)
  have hx171 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x171 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x172 : ℝ := c*c
  have hx172 : Bounds (28180672641 / 1000000000000) (28285521489 / 1000000000000) x172 := by
    apply bounds_mul hc hc <;> norm_num
  let x173 : ℝ := -x172
  have hx173 : Bounds (-28285521489 / 1000000000000) (-28180672641 / 1000000000000) x173 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx172
  let x174 : ℝ := (1 / 1)+x173
  have hx174 : Bounds (971714478511 / 1000000000000) (971819327359 / 1000000000000) x174 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx173 <;> norm_num
  let x175 : ℝ := (1 / 1)-x172
  have hx175 : Bounds (971714478511 / 1000000000000) (971819327359 / 1000000000000) x175 := by
    exact hx174
  let x176 : ℝ := Real.log x175
  have hx176 : Bounds (-5738653 / 200000000) (-28585369 / 1000000000) x176 := by
    exact bounds_log hx175 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (-5738653 / 400000000) (-28585369 / 2000000000) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (-5738653 / 400000000) (-28585369 / 2000000000) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (28585369 / 2000000000) (5738653 / 400000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x171+x180
  have hx181 : Bounds (1414879729 / 2000000000) (1414987627 / 2000000000) x181 := by
    apply bounds_add hx171 hx180 <;> norm_num
  let x182 : ℝ := x171-x179
  have hx182 : Bounds (1414879729 / 2000000000) (1414987627 / 2000000000) x182 := by
    exact hx181
  let x183 : ℝ := Real.log (2 / 1)
  have hx183 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x183 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x184 : ℝ := (1 / 1)+(168183 / 1000000)
  have hx184 : Bounds (1168183 / 1000000) (1168183 / 1000000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((168183 / 1000000) : ℝ)) <;> norm_num
  let x185 : ℝ := (1 / 1)+(168183 / 1000000)
  have hx185 : Bounds (1168183 / 1000000) (1168183 / 1000000) x185 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((168183 / 1000000) : ℝ)) <;> norm_num
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (3108991 / 20000000) (155449551 / 1000000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x187 : ℝ := x184*x186
  have hx187 : Bounds (181593521667 / 1000000000000) (45398380709 / 250000000000) x187 := by
    apply bounds_mul hx184 hx186 <;> norm_num
  let x188 : ℝ := -(168183 / 1000000)
  have hx188 : Bounds (-168183 / 1000000) (-168183 / 1000000) x188 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((168183 / 1000000) : ℝ))
  let x189 : ℝ := (1 / 1)+x188
  have hx189 : Bounds (831817 / 1000000) (831817 / 1000000) x189 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx188 <;> norm_num
  let x190 : ℝ := (1 / 1)-(168183 / 1000000)
  have hx190 : Bounds (831817 / 1000000) (831817 / 1000000) x190 := by
    exact hx189
  let x191 : ℝ := -(168183 / 1000000)
  have hx191 : Bounds (-168183 / 1000000) (-168183 / 1000000) x191 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((168183 / 1000000) : ℝ))
  let x192 : ℝ := (1 / 1)+x191
  have hx192 : Bounds (831817 / 1000000) (831817 / 1000000) x192 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx191 <;> norm_num
  let x193 : ℝ := (1 / 1)-(168183 / 1000000)
  have hx193 : Bounds (831817 / 1000000) (831817 / 1000000) x193 := by
    exact hx192
  let x194 : ℝ := Real.log x193
  have hx194 : Bounds (-36828563 / 200000000) (-92071407 / 500000000) x194 := by
    exact bounds_log hx193 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x195 : ℝ := x190*x194
  have hx195 : Bounds (-30634624789 / 200000000000) (-153173123113 / 1000000000000) x195 := by
    apply bounds_mul hx190 hx194 <;> norm_num
  let x196 : ℝ := x187+x195
  have hx196 : Bounds (14210198861 / 500000000000) (28420399723 / 1000000000000) x196 := by
    apply bounds_add hx187 hx195 <;> norm_num
  let x197 : ℝ := (2 / 1)⁻¹
  have hx197 : Bounds (1 / 2) (1 / 2) x197 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x198 : ℝ := x196*x197
  have hx198 : Bounds (14210198861 / 1000000000000) (7105099931 / 500000000000) x198 := by
    apply bounds_mul hx196 hx197 <;> norm_num
  let x199 : ℝ := x196/(2 / 1)
  have hx199 : Bounds (14210198861 / 1000000000000) (7105099931 / 500000000000) x199 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx198
  let x200 : ℝ := -x199
  have hx200 : Bounds (-7105099931 / 500000000000) (-14210198861 / 1000000000000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx199
  let x201 : ℝ := x183+x200
  have hx201 : Bounds (339468490069 / 500000000000) (678936982139 / 1000000000000) x201 := by
    apply bounds_add hx183 hx200 <;> norm_num
  let x202 : ℝ := x183-x199
  have hx202 : Bounds (339468490069 / 500000000000) (678936982139 / 1000000000000) x202 := by
    exact hx201
  let x203 : ℝ := biasE (168183 / 1000000)
  have hx203 : Bounds (339468490069 / 500000000000) (678936982139 / 1000000000000) x203 := by
    simpa +zetaDelta only [biasE, div_one] using hx202
  let x204 : ℝ := Real.log (2 / 1)
  have hx204 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x204 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x205 : ℝ := (1 / 1)+(167871 / 1000000)
  have hx205 : Bounds (1167871 / 1000000) (1167871 / 1000000) x205 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((167871 / 1000000) : ℝ)) <;> norm_num
  let x206 : ℝ := (1 / 1)+(167871 / 1000000)
  have hx206 : Bounds (1167871 / 1000000) (1167871 / 1000000) x206 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((167871 / 1000000) : ℝ)) <;> norm_num
  let x207 : ℝ := Real.log x206
  have hx207 : Bounds (155182433 / 1000000000) (77591217 / 500000000) x207 := by
    exact bounds_log hx206 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x208 : ℝ := x205*x207
  have hx208 : Bounds (18123306321 / 100000000000) (181233064379 / 1000000000000) x208 := by
    apply bounds_mul hx205 hx207 <;> norm_num
  let x209 : ℝ := -(167871 / 1000000)
  have hx209 : Bounds (-167871 / 1000000) (-167871 / 1000000) x209 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((167871 / 1000000) : ℝ))
  let x210 : ℝ := (1 / 1)+x209
  have hx210 : Bounds (832129 / 1000000) (832129 / 1000000) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx209 <;> norm_num
  let x211 : ℝ := (1 / 1)-(167871 / 1000000)
  have hx211 : Bounds (832129 / 1000000) (832129 / 1000000) x211 := by
    exact hx210
  let x212 : ℝ := -(167871 / 1000000)
  have hx212 : Bounds (-167871 / 1000000) (-167871 / 1000000) x212 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((167871 / 1000000) : ℝ))
  let x213 : ℝ := (1 / 1)+x212
  have hx213 : Bounds (832129 / 1000000) (832129 / 1000000) x213 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx212 <;> norm_num
  let x214 : ℝ := (1 / 1)-(167871 / 1000000)
  have hx214 : Bounds (832129 / 1000000) (832129 / 1000000) x214 := by
    exact hx213
  let x215 : ℝ := Real.log x214
  have hx215 : Bounds (-183767803 / 1000000000) (-91883901 / 500000000) x215 := by
    exact bounds_log hx214 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x216 : ℝ := x211*x215
  have hx216 : Bounds (-152918518143 / 1000000000000) (-15291851731 / 100000000000) x216 := by
    apply bounds_mul hx211 hx215 <;> norm_num
  let x217 : ℝ := x208+x216
  have hx217 : Bounds (28314545067 / 1000000000000) (28314547069 / 1000000000000) x217 := by
    apply bounds_add hx208 hx216 <;> norm_num
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (14157272533 / 1000000000000) (2831454707 / 200000000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (14157272533 / 1000000000000) (2831454707 / 200000000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := -x220
  have hx221 : Bounds (-2831454707 / 200000000000) (-14157272533 / 1000000000000) x221 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx220
  let x222 : ℝ := x204+x221
  have hx222 : Bounds (135797981293 / 200000000000) (678989908467 / 1000000000000) x222 := by
    apply bounds_add hx204 hx221 <;> norm_num
  let x223 : ℝ := x204-x220
  have hx223 : Bounds (135797981293 / 200000000000) (678989908467 / 1000000000000) x223 := by
    exact hx222
  let x224 : ℝ := biasE (167871 / 1000000)
  have hx224 : Bounds (135797981293 / 200000000000) (678989908467 / 1000000000000) x224 := by
    simpa +zetaDelta only [biasE, div_one] using hx223
  let x225 : ℝ := biasE c
  have hx225 : Bounds (339468490069 / 500000000000) (678989908467 / 1000000000000) x225 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx203.1 hx224.2
  let x226 : ℝ := x159⁻¹
  have hx226 : Bounds (2095018183773 / 500000000000) (4197889122939 / 1000000000000) x226 := by
    apply bounds_inv hx159 <;> norm_num
  let x227 : ℝ := x148*x226
  have hx227 : Bounds (1432239718617 / 1000000000000) (17971037661 / 12500000000) x227 := by
    apply bounds_mul hx148 hx226 <;> norm_num
  let x228 : ℝ := x148/x159
  have hx228 : Bounds (1432239718617 / 1000000000000) (17971037661 / 12500000000) x228 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx227
  let x229 : ℝ := c*x148
  have hx229 : Bounds (28690862407 / 500000000000) (28799455521 / 500000000000) x229 := by
    apply bounds_mul hc hx148 <;> norm_num
  let x230 : ℝ := x225+x229
  have hx230 : Bounds (92039838119 / 125000000000) (736588819509 / 1000000000000) x230 := by
    apply bounds_add hx225 hx229 <;> norm_num
  let x231 : ℝ := x*x170
  have hx231 : Bounds (27887262987 / 1000000000000) (27989839459 / 1000000000000) x231 := by
    apply bounds_mul hx hx170 <;> norm_num
  let x232 : ℝ := x48+x231
  have hx232 : Bounds (693345976287 / 1000000000000) (138709758633 / 200000000000) x232 := by
    apply bounds_add hx48 hx231 <;> norm_num
  let x233 : ℝ := x232⁻¹
  have hx233 : Bounds (360464905229 / 250000000000) (288456278453 / 200000000000) x233 := by
    apply bounds_inv hx232 <;> norm_num
  let x234 : ℝ := x230*x233
  have hx234 : Bounds (212333641759 / 200000000000) (1062368348129 / 1000000000000) x234 := by
    apply bounds_mul hx230 hx233 <;> norm_num
  let x235 : ℝ := x230/x232
  have hx235 : Bounds (212333641759 / 200000000000) (1062368348129 / 1000000000000) x235 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx234
  let x236 : ℝ := y*y
  have hx236 : Bounds (54666648481 / 1000000000000) (54864161361 / 1000000000000) x236 := by
    apply bounds_mul hy hy <;> norm_num
  let x237 : ℝ := -x236
  have hx237 : Bounds (-54864161361 / 1000000000000) (-54666648481 / 1000000000000) x237 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx236
  let x238 : ℝ := (1 / 1)+x237
  have hx238 : Bounds (945135838639 / 1000000000000) (945333351519 / 1000000000000) x238 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx237 <;> norm_num
  let x239 : ℝ := (1 / 1)-x236
  have hx239 : Bounds (945135838639 / 1000000000000) (945333351519 / 1000000000000) x239 := by
    exact hx238
  let x240 : ℝ := x239*x159
  have hx240 : Bounds (112572749179 / 500000000000) (22561459343 / 100000000000) x240 := by
    apply bounds_mul hx239 hx159 <;> norm_num
  let x241 : ℝ := c*c
  have hx241 : Bounds (28180672641 / 1000000000000) (28285521489 / 1000000000000) x241 := by
    apply bounds_mul hc hc <;> norm_num
  let x242 : ℝ := -x241
  have hx242 : Bounds (-28285521489 / 1000000000000) (-28180672641 / 1000000000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx241
  let x243 : ℝ := (1 / 1)+x242
  have hx243 : Bounds (971714478511 / 1000000000000) (971819327359 / 1000000000000) x243 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx242 <;> norm_num
  let x244 : ℝ := (1 / 1)-x241
  have hx244 : Bounds (971714478511 / 1000000000000) (971819327359 / 1000000000000) x244 := by
    exact hx243
  let x245 : ℝ := x244*x182
  have hx245 : Bounds (68742955901 / 100000000000) (687556161947 / 1000000000000) x245 := by
    apply bounds_mul hx244 hx182 <;> norm_num
  let x246 : ℝ := y*y
  have hx246 : Bounds (54666648481 / 1000000000000) (54864161361 / 1000000000000) x246 := by
    apply bounds_mul hy hy <;> norm_num
  let x247 : ℝ := (1 / 1)+x246
  have hx247 : Bounds (1054666648481 / 1000000000000) (1054864161361 / 1000000000000) x247 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx246 <;> norm_num
  let x248 : ℝ := x247*x159
  have hx248 : Bounds (251237376117 / 1000000000000) (125877685637 / 500000000000) x248 := by
    apply bounds_mul hx247 hx159 <;> norm_num
  let x249 : ℝ := -y
  have hx249 : Bounds (-234231 / 1000000) (-233809 / 1000000) x249 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x250 : ℝ := x248+x249
  have hx250 : Bounds (17006376117 / 1000000000000) (8973185637 / 500000000000) x250 := by
    apply bounds_add hx248 hx249 <;> norm_num
  let x251 : ℝ := x248-y
  have hx251 : Bounds (17006376117 / 1000000000000) (8973185637 / 500000000000) x251 := by
    exact hx250
  let x252 : ℝ := x240*x240
  have hx252 : Bounds (5069049543 / 100000000000) (50901944769 / 1000000000000) x252 := by
    apply bounds_mul hx240 hx240 <;> norm_num
  let x253 : ℝ := x252⁻¹
  have hx253 : Bounds (1964561480977 / 100000000000) (3945512828459 / 200000000000) x253 := by
    apply bounds_inv hx252 <;> norm_num
  let x254 : ℝ := x251*x253
  have hx254 : Bounds (41762589313 / 125000000000) (35403819043 / 100000000000) x254 := by
    apply bounds_mul hx251 hx253 <;> norm_num
  let x255 : ℝ := x251/x252
  have hx255 : Bounds (41762589313 / 125000000000) (35403819043 / 100000000000) x255 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx254
  let x256 : ℝ := (-2 / 1)*x255
  have hx256 : Bounds (-35403819043 / 50000000000) (-41762589313 / 62500000000) x256 := by
    apply bounds_mul (bounds_const ((-2 / 1) : ℝ)) hx255 <;> norm_num
  let x257 : ℝ := x256*x228
  have hx257 : Bounds (-127248673073 / 125000000000) (-957024626661 / 1000000000000) x257 := by
    apply bounds_mul hx256 hx228 <;> norm_num
  let x258 : ℝ := (2 / 1)*x182
  have hx258 : Bounds (1414879729 / 1000000000) (1414987627 / 1000000000) x258 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx182 <;> norm_num
  let x259 : ℝ := c*c
  have hx259 : Bounds (28180672641 / 1000000000000) (28285521489 / 1000000000000) x259 := by
    apply bounds_mul hc hc <;> norm_num
  let x260 : ℝ := -x259
  have hx260 : Bounds (-28285521489 / 1000000000000) (-28180672641 / 1000000000000) x260 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx259
  let x261 : ℝ := x258+x260
  have hx261 : Bounds (1386594207511 / 1000000000000) (1386806954359 / 1000000000000) x261 := by
    apply bounds_add hx258 hx260 <;> norm_num
  let x262 : ℝ := x258-x259
  have hx262 : Bounds (1386594207511 / 1000000000000) (1386806954359 / 1000000000000) x262 := by
    exact hx261
  let x263 : ℝ := c*x262
  have hx263 : Bounds (232768956209 / 1000000000000) (46647470801 / 200000000000) x263 := by
    apply bounds_mul hc hx262 <;> norm_num
  let x264 : ℝ := x245*x245
  have hx264 : Bounds (2362796993 / 5000000000) (59091684479 / 125000000000) x264 := by
    apply bounds_mul hx245 hx245 <;> norm_num
  let x265 : ℝ := x264⁻¹
  have hx265 : Bounds (528839214443 / 250000000000) (423227218827 / 200000000000) x265 := by
    apply bounds_inv hx264 <;> norm_num
  let x266 : ℝ := x263*x265
  have hx266 : Bounds (492389407793 / 1000000000000) (493561983311 / 1000000000000) x266 := by
    apply bounds_mul hx263 hx265 <;> norm_num
  let x267 : ℝ := x263/x264
  have hx267 : Bounds (492389407793 / 1000000000000) (493561983311 / 1000000000000) x267 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx266
  let x268 : ℝ := (2 / 1)*x267
  have hx268 : Bounds (492389407793 / 500000000000) (493561983311 / 500000000000) x268 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx267 <;> norm_num
  let x269 : ℝ := x268*x235
  have hx269 : Bounds (522754180601 / 500000000000) (1048689257819 / 1000000000000) x269 := by
    apply bounds_mul hx268 hx235 <;> norm_num
  let x270 : ℝ := x257+x269
  have hx270 : Bounds (13759488309 / 500000000000) (45832315579 / 500000000000) x270 := by
    apply bounds_add hx257 hx269 <;> norm_num
  have hPos : 0 < x270 :=
    lt_of_lt_of_le (by norm_num) hx270.1
  have hBridgeL : doubleCapBridgeL x = x48 := by
    exact hEll'
  rw [← doubleCapBridgeDerivativeTraceForm_eq x]
  simpa +zetaDelta only [doubleCapBridgeDerivativeTraceForm,
    hBridgeL, SmallMean.A, biasB, div_one, pow_two] using hPos

theorem acceptedCell : DoubleCapBridgeDerivativeCellCertificate
    (⟨135, by decide⟩ : Fin 256) doubleCapBridgeDerivativeExpression where
  positive x hx := by
    have hloEq : doubleCapBridgeLo (⟨135, by decide⟩ : Fin 256) =
        (337 / 2048) := by norm_num [doubleCapBridgeLo, doubleCapBridgeStep]
    have hhiEq : doubleCapBridgeHi (⟨135, by decide⟩ : Fin 256) =
        (211 / 1280) := by norm_num [doubleCapBridgeHi, doubleCapBridgeStep]
    have hlo : (337 / 2048) ≤ x := by
      simpa only [hloEq] using hx.1
    have hhi : x ≤ (211 / 1280) := by
      simpa only [hhiEq] using hx.2
    exact cell_derivative_pos x ⟨hlo, hhi⟩

#print axioms cell_derivative_pos
#print axioms acceptedCell

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell135

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell136 =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell136
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_derivative_pos (x : ℝ)
    (hx : Bounds (211 / 1280) (1691 / 10240) x) :
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
  have hx0 : Bounds (211 / 640) (1691 / 5120) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx <;> norm_num
  let x1 : ℝ := Real.log (2 / 1)
  have hx1 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x1 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x2 : ℝ := Real.log (2 / 1)
  have hx2 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x2 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x3 : ℝ := (1 / 1)+(1691 / 5120)
  have hx3 : Bounds (6811 / 5120) (6811 / 5120) x3 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1691 / 5120) : ℝ)) <;> norm_num
  let x4 : ℝ := (1 / 1)+(1691 / 5120)
  have hx4 : Bounds (6811 / 5120) (6811 / 5120) x4 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1691 / 5120) : ℝ)) <;> norm_num
  let x5 : ℝ := Real.log x4
  have hx5 : Bounds (285384513 / 1000000000) (142692257 / 500000000) x5 := by
    exact bounds_log hx4 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x6 : ℝ := x3*x5
  have hx6 : Bounds (379639437117 / 1000000000000) (379639438449 / 1000000000000) x6 := by
    apply bounds_mul hx3 hx5 <;> norm_num
  let x7 : ℝ := -(1691 / 5120)
  have hx7 : Bounds (-1691 / 5120) (-1691 / 5120) x7 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1691 / 5120) : ℝ))
  let x8 : ℝ := (1 / 1)+x7
  have hx8 : Bounds (3429 / 5120) (3429 / 5120) x8 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx7 <;> norm_num
  let x9 : ℝ := (1 / 1)-(1691 / 5120)
  have hx9 : Bounds (3429 / 5120) (3429 / 5120) x9 := by
    exact hx8
  let x10 : ℝ := -(1691 / 5120)
  have hx10 : Bounds (-1691 / 5120) (-1691 / 5120) x10 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1691 / 5120) : ℝ))
  let x11 : ℝ := (1 / 1)+x10
  have hx11 : Bounds (3429 / 5120) (3429 / 5120) x11 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx10 <;> norm_num
  let x12 : ℝ := (1 / 1)-(1691 / 5120)
  have hx12 : Bounds (3429 / 5120) (3429 / 5120) x12 := by
    exact hx11
  let x13 : ℝ := Real.log x12
  have hx13 : Bounds (-200442883 / 500000000) (-80177153 / 200000000) x13 := by
    exact bounds_log hx12 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x14 : ℝ := x9*x13
  have hx14 : Bounds (-268483846019 / 1000000000000) (-67120961337 / 250000000000) x14 := by
    apply bounds_mul hx9 hx13 <;> norm_num
  let x15 : ℝ := x6+x14
  have hx15 : Bounds (55577795549 / 500000000000) (111155593101 / 1000000000000) x15 := by
    apply bounds_add hx6 hx14 <;> norm_num
  let x16 : ℝ := (2 / 1)⁻¹
  have hx16 : Bounds (1 / 2) (1 / 2) x16 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x17 : ℝ := x15*x16
  have hx17 : Bounds (55577795549 / 1000000000000) (55577796551 / 1000000000000) x17 := by
    apply bounds_mul hx15 hx16 <;> norm_num
  let x18 : ℝ := x15/(2 / 1)
  have hx18 : Bounds (55577795549 / 1000000000000) (55577796551 / 1000000000000) x18 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx17
  let x19 : ℝ := -x18
  have hx19 : Bounds (-55577796551 / 1000000000000) (-55577795549 / 1000000000000) x19 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx18
  let x20 : ℝ := x2+x19
  have hx20 : Bounds (637569383449 / 1000000000000) (637569385451 / 1000000000000) x20 := by
    apply bounds_add hx2 hx19 <;> norm_num
  let x21 : ℝ := x2-x18
  have hx21 : Bounds (637569383449 / 1000000000000) (637569385451 / 1000000000000) x21 := by
    exact hx20
  let x22 : ℝ := biasE (1691 / 5120)
  have hx22 : Bounds (637569383449 / 1000000000000) (637569385451 / 1000000000000) x22 := by
    simpa +zetaDelta only [biasE, div_one] using hx21
  let x23 : ℝ := Real.log (2 / 1)
  have hx23 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x23 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x24 : ℝ := (1 / 1)+(211 / 640)
  have hx24 : Bounds (851 / 640) (851 / 640) x24 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((211 / 640) : ℝ)) <;> norm_num
  let x25 : ℝ := (1 / 1)+(211 / 640)
  have hx25 : Bounds (851 / 640) (851 / 640) x25 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((211 / 640) : ℝ)) <;> norm_num
  let x26 : ℝ := Real.log x25
  have hx26 : Bounds (17808997 / 62500000) (284943953 / 1000000000) x26 := by
    exact bounds_log hx25 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x27 : ℝ := x24*x26
  have hx27 : Bounds (15155456447 / 40000000000) (75777282501 / 200000000000) x27 := by
    apply bounds_mul hx24 hx26 <;> norm_num
  let x28 : ℝ := -(211 / 640)
  have hx28 : Bounds (-211 / 640) (-211 / 640) x28 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((211 / 640) : ℝ))
  let x29 : ℝ := (1 / 1)+x28
  have hx29 : Bounds (429 / 640) (429 / 640) x29 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx28 <;> norm_num
  let x30 : ℝ := (1 / 1)-(211 / 640)
  have hx30 : Bounds (429 / 640) (429 / 640) x30 := by
    exact hx29
  let x31 : ℝ := -(211 / 640)
  have hx31 : Bounds (-211 / 640) (-211 / 640) x31 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((211 / 640) : ℝ))
  let x32 : ℝ := (1 / 1)+x31
  have hx32 : Bounds (429 / 640) (429 / 640) x32 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx31 <;> norm_num
  let x33 : ℝ := (1 / 1)-(211 / 640)
  have hx33 : Bounds (429 / 640) (429 / 640) x33 := by
    exact hx32
  let x34 : ℝ := Real.log x33
  have hx34 : Bounds (-200005629 / 500000000) (-400011257 / 1000000000) x34 := by
    exact bounds_log hx33 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x35 : ℝ := x30*x34
  have hx35 : Bounds (-268132546379 / 1000000000000) (-268132545707 / 1000000000000) x35 := by
    apply bounds_mul hx30 hx34 <;> norm_num
  let x36 : ℝ := x27+x35
  have hx36 : Bounds (27688466199 / 250000000000) (55376933399 / 500000000000) x36 := by
    apply bounds_add hx27 hx35 <;> norm_num
  let x37 : ℝ := (2 / 1)⁻¹
  have hx37 : Bounds (1 / 2) (1 / 2) x37 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x38 : ℝ := x36*x37
  have hx38 : Bounds (27688466199 / 500000000000) (55376933399 / 1000000000000) x38 := by
    apply bounds_mul hx36 hx37 <;> norm_num
  let x39 : ℝ := x36/(2 / 1)
  have hx39 : Bounds (27688466199 / 500000000000) (55376933399 / 1000000000000) x39 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx38
  let x40 : ℝ := -x39
  have hx40 : Bounds (-55376933399 / 1000000000000) (-27688466199 / 500000000000) x40 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx39
  let x41 : ℝ := x23+x40
  have hx41 : Bounds (637770246601 / 1000000000000) (318885124301 / 500000000000) x41 := by
    apply bounds_add hx23 hx40 <;> norm_num
  let x42 : ℝ := x23-x39
  have hx42 : Bounds (637770246601 / 1000000000000) (318885124301 / 500000000000) x42 := by
    exact hx41
  let x43 : ℝ := biasE (211 / 640)
  have hx43 : Bounds (637770246601 / 1000000000000) (318885124301 / 500000000000) x43 := by
    simpa +zetaDelta only [biasE, div_one] using hx42
  let x44 : ℝ := biasE x0
  have hx44 : Bounds (637569383449 / 1000000000000) (318885124301 / 500000000000) x44 := by
    exact bounds_biasE hx0 (by norm_num) (by norm_num) hx22.1 hx43.2
  let x45 : ℝ := x1+x44
  have hx45 : Bounds (1330716563449 / 1000000000000) (665458714801 / 500000000000) x45 := by
    apply bounds_add hx1 hx44 <;> norm_num
  let x46 : ℝ := (2 / 1)⁻¹
  have hx46 : Bounds (1 / 2) (1 / 2) x46 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x47 : ℝ := x45*x46
  have hx47 : Bounds (166339570431 / 250000000000) (665458714801 / 1000000000000) x47 := by
    apply bounds_mul hx45 hx46 <;> norm_num
  let x48 : ℝ := x45/(2 / 1)
  have hx48 : Bounds (166339570431 / 250000000000) (665458714801 / 1000000000000) x48 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx47
  let x49 : ℝ := Real.log (2 / 1)
  have hx49 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x49 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x50 : ℝ := (1 / 1)+(23423 / 100000)
  have hx50 : Bounds (123423 / 100000) (123423 / 100000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((23423 / 100000) : ℝ)) <;> norm_num
  let x51 : ℝ := (1 / 1)+(23423 / 100000)
  have hx51 : Bounds (123423 / 100000) (123423 / 100000) x51 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((23423 / 100000) : ℝ)) <;> norm_num
  let x52 : ℝ := Real.log x51
  have hx52 : Bounds (210447293 / 1000000000) (105223647 / 500000000) x52 := by
    exact bounds_log hx51 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x53 : ℝ := x50*x52
  have hx53 : Bounds (259740362439 / 1000000000000) (129870181837 / 500000000000) x53 := by
    apply bounds_mul hx50 hx52 <;> norm_num
  let x54 : ℝ := -(23423 / 100000)
  have hx54 : Bounds (-23423 / 100000) (-23423 / 100000) x54 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((23423 / 100000) : ℝ))
  let x55 : ℝ := (1 / 1)+x54
  have hx55 : Bounds (76577 / 100000) (76577 / 100000) x55 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx54 <;> norm_num
  let x56 : ℝ := (1 / 1)-(23423 / 100000)
  have hx56 : Bounds (76577 / 100000) (76577 / 100000) x56 := by
    exact hx55
  let x57 : ℝ := -(23423 / 100000)
  have hx57 : Bounds (-23423 / 100000) (-23423 / 100000) x57 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((23423 / 100000) : ℝ))
  let x58 : ℝ := (1 / 1)+x57
  have hx58 : Bounds (76577 / 100000) (76577 / 100000) x58 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx57 <;> norm_num
  let x59 : ℝ := (1 / 1)-(23423 / 100000)
  have hx59 : Bounds (76577 / 100000) (76577 / 100000) x59 := by
    exact hx58
  let x60 : ℝ := Real.log x59
  have hx60 : Bounds (-33359177 / 125000000) (-53374683 / 200000000) x60 := by
    exact bounds_log hx59 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x61 : ℝ := x56*x60
  have hx61 : Bounds (-204363655771 / 1000000000000) (-51090913751 / 250000000000) x61 := by
    apply bounds_mul hx56 hx60 <;> norm_num
  let x62 : ℝ := x53+x61
  have hx62 : Bounds (13844176667 / 250000000000) (5537670867 / 100000000000) x62 := by
    apply bounds_add hx53 hx61 <;> norm_num
  let x63 : ℝ := (2 / 1)⁻¹
  have hx63 : Bounds (1 / 2) (1 / 2) x63 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x64 : ℝ := x62*x63
  have hx64 : Bounds (13844176667 / 500000000000) (5537670867 / 200000000000) x64 := by
    apply bounds_mul hx62 hx63 <;> norm_num
  let x65 : ℝ := x62/(2 / 1)
  have hx65 : Bounds (13844176667 / 500000000000) (5537670867 / 200000000000) x65 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx64
  let x66 : ℝ := -x65
  have hx66 : Bounds (-5537670867 / 200000000000) (-13844176667 / 500000000000) x66 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx65
  let x67 : ℝ := x49+x66
  have hx67 : Bounds (133091765133 / 200000000000) (332729413833 / 500000000000) x67 := by
    apply bounds_add hx49 hx66 <;> norm_num
  let x68 : ℝ := x49-x65
  have hx68 : Bounds (133091765133 / 200000000000) (332729413833 / 500000000000) x68 := by
    exact hx67
  let x69 : ℝ := biasE (23423 / 100000)
  have hx69 : Bounds (133091765133 / 200000000000) (332729413833 / 500000000000) x69 := by
    simpa +zetaDelta only [biasE, div_one] using hx68
  let x70 : ℝ := Real.log (2 / 1)
  have hx70 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x70 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x71 : ℝ := (1 / 1)+(234651 / 1000000)
  have hx71 : Bounds (1234651 / 1000000) (1234651 / 1000000) x71 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((234651 / 1000000) : ℝ)) <;> norm_num
  let x72 : ℝ := (1 / 1)+(234651 / 1000000)
  have hx72 : Bounds (1234651 / 1000000) (1234651 / 1000000) x72 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((234651 / 1000000) : ℝ)) <;> norm_num
  let x73 : ℝ := Real.log x72
  have hx73 : Bounds (210788339 / 1000000000) (10539417 / 50000000) x73 := by
    exact bounds_log hx72 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x74 : ℝ := x71*x73
  have hx74 : Bounds (130125016767 / 500000000000) (26025003477 / 100000000000) x74 := by
    apply bounds_mul hx71 hx73 <;> norm_num
  let x75 : ℝ := -(234651 / 1000000)
  have hx75 : Bounds (-234651 / 1000000) (-234651 / 1000000) x75 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((234651 / 1000000) : ℝ))
  let x76 : ℝ := (1 / 1)+x75
  have hx76 : Bounds (765349 / 1000000) (765349 / 1000000) x76 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx75 <;> norm_num
  let x77 : ℝ := (1 / 1)-(234651 / 1000000)
  have hx77 : Bounds (765349 / 1000000) (765349 / 1000000) x77 := by
    exact hx76
  let x78 : ℝ := -(234651 / 1000000)
  have hx78 : Bounds (-234651 / 1000000) (-234651 / 1000000) x78 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((234651 / 1000000) : ℝ))
  let x79 : ℝ := (1 / 1)+x78
  have hx79 : Bounds (765349 / 1000000) (765349 / 1000000) x79 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx78 <;> norm_num
  let x80 : ℝ := (1 / 1)-(234651 / 1000000)
  have hx80 : Bounds (765349 / 1000000) (765349 / 1000000) x80 := by
    exact hx79
  let x81 : ℝ := Real.log x80
  have hx81 : Bounds (-267423341 / 1000000000) (-13371167 / 50000000) x81 := by
    exact bounds_log hx80 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x82 : ℝ := x77*x81
  have hx82 : Bounds (-51168046653 / 250000000000) (-40934437169 / 200000000000) x82 := by
    apply bounds_mul hx77 hx81 <;> norm_num
  let x83 : ℝ := x74+x82
  have hx83 : Bounds (27788923461 / 500000000000) (2223113957 / 40000000000) x83 := by
    apply bounds_add hx74 hx82 <;> norm_num
  let x84 : ℝ := (2 / 1)⁻¹
  have hx84 : Bounds (1 / 2) (1 / 2) x84 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x85 : ℝ := x83*x84
  have hx85 : Bounds (27788923461 / 1000000000000) (27788924463 / 1000000000000) x85 := by
    apply bounds_mul hx83 hx84 <;> norm_num
  let x86 : ℝ := x83/(2 / 1)
  have hx86 : Bounds (27788923461 / 1000000000000) (27788924463 / 1000000000000) x86 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx85
  let x87 : ℝ := -x86
  have hx87 : Bounds (-27788924463 / 1000000000000) (-27788923461 / 1000000000000) x87 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx86
  let x88 : ℝ := x70+x87
  have hx88 : Bounds (665358255537 / 1000000000000) (665358257539 / 1000000000000) x88 := by
    apply bounds_add hx70 hx87 <;> norm_num
  let x89 : ℝ := x70-x86
  have hx89 : Bounds (665358255537 / 1000000000000) (665358257539 / 1000000000000) x89 := by
    exact hx88
  let x90 : ℝ := biasE (234651 / 1000000)
  have hx90 : Bounds (665358255537 / 1000000000000) (665358257539 / 1000000000000) x90 := by
    simpa +zetaDelta only [biasE, div_one] using hx89
  let y : ℝ := doubleCapHighTailY x
  have hEll' : Real.log 2 * doubleCapHighTailFloor x = x48 := by
    simpa +zetaDelta only [div_one] using hEll
  have hy : Bounds (23423 / 100000) (234651 / 1000000) y := by
    dsimp only [y, doubleCapHighTailY]
    apply entropyInverseBias_bracket hh0.le hh1.le
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (234651 / 1000000) ≤ (665358257539 / 1000000000000) := hx90.2
      have h2 : (166339570431 / 250000000000) ≤ x48 := hx48.1
      linarith [hEll']
    · have h1 : x48 ≤ (665458714801 / 1000000000000) := hx48.2
      have h2 : (133091765133 / 200000000000) ≤ biasE (23423 / 100000) := hx69.1
      linarith [hEll']
  let x91 : ℝ := x⁻¹
  have hx91 : Bounds (242223536369 / 40000000000) (6066350710901 / 1000000000000) x91 := by
    apply bounds_inv hx <;> norm_num
  let x92 : ℝ := x48*x91
  have hx92 : Bounds (4029135898789 / 1000000000000) (4036905947609 / 1000000000000) x92 := by
    apply bounds_mul hx48 hx91 <;> norm_num
  let x93 : ℝ := x48/x
  have hx93 : Bounds (4029135898789 / 1000000000000) (4036905947609 / 1000000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(84091 / 500000)
  have hx95 : Bounds (584091 / 500000) (584091 / 500000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((84091 / 500000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(84091 / 500000)
  have hx96 : Bounds (584091 / 500000) (584091 / 500000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((84091 / 500000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (77724347 / 500000000) (31089739 / 200000000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (90796183127 / 500000000000) (181592367423 / 1000000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(84091 / 500000)
  have hx99 : Bounds (-84091 / 500000) (-84091 / 500000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((84091 / 500000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (415909 / 500000) (415909 / 500000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(84091 / 500000)
  have hx101 : Bounds (415909 / 500000) (415909 / 500000) x101 := by
    exact hx100
  let x102 : ℝ := -(84091 / 500000)
  have hx102 : Bounds (-84091 / 500000) (-84091 / 500000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((84091 / 500000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (415909 / 500000) (415909 / 500000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(84091 / 500000)
  have hx104 : Bounds (415909 / 500000) (415909 / 500000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-184141613 / 1000000000) (-46035403 / 250000000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-153172308243 / 1000000000000) (-15317230741 / 100000000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (28420058011 / 1000000000000) (28420060013 / 1000000000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (2842005801 / 200000000000) (14210030007 / 1000000000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (2842005801 / 200000000000) (14210030007 / 1000000000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-14210030007 / 1000000000000) (-2842005801 / 200000000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (678937149993 / 1000000000000) (135787430399 / 200000000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (678937149993 / 1000000000000) (135787430399 / 200000000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (84091 / 500000)
  have hx114 : Bounds (678937149993 / 1000000000000) (135787430399 / 200000000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(84247 / 500000)
  have hx116 : Bounds (584247 / 500000) (584247 / 500000) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((84247 / 500000) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(84247 / 500000)
  have hx117 : Bounds (584247 / 500000) (584247 / 500000) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((84247 / 500000) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (7785787 / 50000000) (155715741 / 1000000000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (36390581579 / 200000000000) (36390581813 / 200000000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(84247 / 500000)
  have hx120 : Bounds (-84247 / 500000) (-84247 / 500000) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((84247 / 500000) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (415753 / 500000) (415753 / 500000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(84247 / 500000)
  have hx122 : Bounds (415753 / 500000) (415753 / 500000) x122 := by
    exact hx121
  let x123 : ℝ := -(84247 / 500000)
  have hx123 : Bounds (-84247 / 500000) (-84247 / 500000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((84247 / 500000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (415753 / 500000) (415753 / 500000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(84247 / 500000)
  have hx125 : Bounds (415753 / 500000) (415753 / 500000) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-36903353 / 200000000) (-46129191 / 250000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-153426797199 / 1000000000000) (-76713398183 / 500000000000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (3565763837 / 125000000000) (28526112699 / 1000000000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (3565763837 / 250000000000) (285261127 / 20000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (3565763837 / 250000000000) (285261127 / 20000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-285261127 / 20000000000) (-3565763837 / 250000000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (13577682473 / 20000000000) (169721031413 / 250000000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (13577682473 / 20000000000) (169721031413 / 250000000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (84247 / 500000)
  have hx135 : Bounds (13577682473 / 20000000000) (169721031413 / 250000000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(84091 / 500000)
  have hx136 : Bounds (67762813373 / 100000000000) (678934916081 / 1000000000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((84091 / 500000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(84247 / 500000)
  have hx137 : Bounds (67888522413 / 100000000000) (680194430737 / 1000000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((84247 / 500000) : ℝ)) <;> norm_num
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
  have hc : Bounds (84091 / 500000) (84247 / 500000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num)
      (by norm_num) (show 0 < x93 by linarith [hx93.1]) hcEq
    · have h1 : x93 * (84091 / 500000) ≤ (678934916081 / 1000000000000) := hx136.2
      have h2 : (678937149993 / 1000000000000) ≤ biasE (84091 / 500000) := hx114.1
      linarith
    · have h1 : biasE (84247 / 500000) ≤ (169721031413 / 250000000000) := hx135.2
      have h2 : (67888522413 / 100000000000) ≤ x93 * (84247 / 500000) := hx137.1
      linarith
  let x138 : ℝ := (1 / 1)+x0
  have hx138 : Bounds (851 / 640) (6811 / 5120) x138 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx0 <;> norm_num
  let x139 : ℝ := -x0
  have hx139 : Bounds (-1691 / 5120) (-211 / 640) x139 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x140 : ℝ := (1 / 1)+x139
  have hx140 : Bounds (3429 / 5120) (429 / 640) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx139 <;> norm_num
  let x141 : ℝ := (1 / 1)-x0
  have hx141 : Bounds (3429 / 5120) (429 / 640) x141 := by
    exact hx140
  let x142 : ℝ := x141⁻¹
  have hx142 : Bounds (1491841491841 / 1000000000000) (746573344999 / 500000000000) x142 := by
    apply bounds_inv hx141 <;> norm_num
  let x143 : ℝ := x138*x142
  have hx143 : Bounds (991841491841 / 500000000000) (496573344999 / 250000000000) x143 := by
    apply bounds_mul hx138 hx142 <;> norm_num
  let x144 : ℝ := x138/x141
  have hx144 : Bounds (991841491841 / 500000000000) (496573344999 / 250000000000) x144 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx143
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (684955209 / 1000000000) (686270279 / 1000000000) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_14.2)
  let x146 : ℝ := (2 / 1)⁻¹
  have hx146 : Bounds (1 / 2) (1 / 2) x146 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x147 : ℝ := x145*x146
  have hx147 : Bounds (684955209 / 2000000000) (686270279 / 2000000000) x147 := by
    apply bounds_mul hx145 hx146 <;> norm_num
  let x148 : ℝ := x145/(2 / 1)
  have hx148 : Bounds (684955209 / 2000000000) (686270279 / 2000000000) x148 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx147
  let x149 : ℝ := (1 / 1)+y
  have hx149 : Bounds (123423 / 100000) (1234651 / 1000000) x149 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x150 : ℝ := -y
  have hx150 : Bounds (-234651 / 1000000) (-23423 / 100000) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (765349 / 1000000) (76577 / 100000) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-y
  have hx152 : Bounds (765349 / 1000000) (76577 / 100000) x152 := by
    exact hx151
  let x153 : ℝ := x152⁻¹
  have hx153 : Bounds (1305875132219 / 1000000000000) (1306593462591 / 1000000000000) x153 := by
    apply bounds_inv hx152 <;> norm_num
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (805875132219 / 500000000000) (806593462591 / 500000000000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x149/x152
  have hx155 : Bounds (805875132219 / 500000000000) (806593462591 / 500000000000) x155 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx154
  let x156 : ℝ := Real.log x155
  have hx156 : Bounds (477320709 / 1000000000) (2988823 / 6250000) x156 := by
    exact bounds_log hx155 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_16.2)
  let x157 : ℝ := (2 / 1)⁻¹
  have hx157 : Bounds (1 / 2) (1 / 2) x157 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x158 : ℝ := x156*x157
  have hx158 : Bounds (477320709 / 2000000000) (2988823 / 12500000) x158 := by
    apply bounds_mul hx156 hx157 <;> norm_num
  let x159 : ℝ := x156/(2 / 1)
  have hx159 : Bounds (477320709 / 2000000000) (2988823 / 12500000) x159 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx158
  let x160 : ℝ := (1 / 1)+c
  have hx160 : Bounds (584091 / 500000) (584247 / 500000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x161 : ℝ := -c
  have hx161 : Bounds (-84247 / 500000) (-84091 / 500000) x161 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x162 : ℝ := (1 / 1)+x161
  have hx162 : Bounds (415753 / 500000) (415909 / 500000) x162 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx161 <;> norm_num
  let x163 : ℝ := (1 / 1)-c
  have hx163 : Bounds (415753 / 500000) (415909 / 500000) x163 := by
    exact hx162
  let x164 : ℝ := x163⁻¹
  have hx164 : Bounds (601093027561 / 500000000000) (1202637142727 / 1000000000000) x164 := by
    apply bounds_inv hx163 <;> norm_num
  let x165 : ℝ := x160*x164
  have hx165 : Bounds (351093027561 / 250000000000) (702637142727 / 500000000000) x165 := by
    apply bounds_mul hx160 hx164 <;> norm_num
  let x166 : ℝ := x160/x163
  have hx166 : Bounds (351093027561 / 250000000000) (702637142727 / 500000000000) x166 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx165
  let x167 : ℝ := Real.log x166
  have hx167 : Bounds (169795153 / 500000000) (68046501 / 200000000) x167 := by
    exact bounds_log hx166 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x168 : ℝ := (2 / 1)⁻¹
  have hx168 : Bounds (1 / 2) (1 / 2) x168 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x169 : ℝ := x167*x168
  have hx169 : Bounds (169795153 / 1000000000) (68046501 / 400000000) x169 := by
    apply bounds_mul hx167 hx168 <;> norm_num
  let x170 : ℝ := x167/(2 / 1)
  have hx170 : Bounds (169795153 / 1000000000) (68046501 / 400000000) x170 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx169
  let x171 : ℝ := Real.log (2 / 1)
  have hx171 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x171 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x172 : ℝ := c*c
  have hx172 : Bounds (7071296281 / 250000000000) (7097557009 / 250000000000) x172 := by
    apply bounds_mul hc hc <;> norm_num
  let x173 : ℝ := -x172
  have hx173 : Bounds (-7097557009 / 250000000000) (-7071296281 / 250000000000) x173 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx172
  let x174 : ℝ := (1 / 1)+x173
  have hx174 : Bounds (242902442991 / 250000000000) (242928703719 / 250000000000) x174 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx173 <;> norm_num
  let x175 : ℝ := (1 / 1)-x172
  have hx175 : Bounds (242902442991 / 250000000000) (242928703719 / 250000000000) x175 := by
    exact hx174
  let x176 : ℝ := Real.log x175
  have hx176 : Bounds (-1152041 / 40000000) (-28692917 / 1000000000) x176 := by
    exact bounds_log hx175 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (-1152041 / 80000000) (-28692917 / 2000000000) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (-1152041 / 80000000) (-28692917 / 2000000000) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (28692917 / 2000000000) (1152041 / 80000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x171+x180
  have hx181 : Bounds (1414987277 / 2000000000) (1415095387 / 2000000000) x181 := by
    apply bounds_add hx171 hx180 <;> norm_num
  let x182 : ℝ := x171-x179
  have hx182 : Bounds (1414987277 / 2000000000) (1415095387 / 2000000000) x182 := by
    exact hx181
  let x183 : ℝ := Real.log (2 / 1)
  have hx183 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x183 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x184 : ℝ := (1 / 1)+(84247 / 500000)
  have hx184 : Bounds (584247 / 500000) (584247 / 500000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((84247 / 500000) : ℝ)) <;> norm_num
  let x185 : ℝ := (1 / 1)+(84247 / 500000)
  have hx185 : Bounds (584247 / 500000) (584247 / 500000) x185 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((84247 / 500000) : ℝ)) <;> norm_num
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (7785787 / 50000000) (155715741 / 1000000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x187 : ℝ := x184*x186
  have hx187 : Bounds (36390581579 / 200000000000) (36390581813 / 200000000000) x187 := by
    apply bounds_mul hx184 hx186 <;> norm_num
  let x188 : ℝ := -(84247 / 500000)
  have hx188 : Bounds (-84247 / 500000) (-84247 / 500000) x188 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((84247 / 500000) : ℝ))
  let x189 : ℝ := (1 / 1)+x188
  have hx189 : Bounds (415753 / 500000) (415753 / 500000) x189 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx188 <;> norm_num
  let x190 : ℝ := (1 / 1)-(84247 / 500000)
  have hx190 : Bounds (415753 / 500000) (415753 / 500000) x190 := by
    exact hx189
  let x191 : ℝ := -(84247 / 500000)
  have hx191 : Bounds (-84247 / 500000) (-84247 / 500000) x191 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((84247 / 500000) : ℝ))
  let x192 : ℝ := (1 / 1)+x191
  have hx192 : Bounds (415753 / 500000) (415753 / 500000) x192 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx191 <;> norm_num
  let x193 : ℝ := (1 / 1)-(84247 / 500000)
  have hx193 : Bounds (415753 / 500000) (415753 / 500000) x193 := by
    exact hx192
  let x194 : ℝ := Real.log x193
  have hx194 : Bounds (-36903353 / 200000000) (-46129191 / 250000000) x194 := by
    exact bounds_log hx193 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x195 : ℝ := x190*x194
  have hx195 : Bounds (-153426797199 / 1000000000000) (-76713398183 / 500000000000) x195 := by
    apply bounds_mul hx190 hx194 <;> norm_num
  let x196 : ℝ := x187+x195
  have hx196 : Bounds (3565763837 / 125000000000) (28526112699 / 1000000000000) x196 := by
    apply bounds_add hx187 hx195 <;> norm_num
  let x197 : ℝ := (2 / 1)⁻¹
  have hx197 : Bounds (1 / 2) (1 / 2) x197 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x198 : ℝ := x196*x197
  have hx198 : Bounds (3565763837 / 250000000000) (285261127 / 20000000000) x198 := by
    apply bounds_mul hx196 hx197 <;> norm_num
  let x199 : ℝ := x196/(2 / 1)
  have hx199 : Bounds (3565763837 / 250000000000) (285261127 / 20000000000) x199 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx198
  let x200 : ℝ := -x199
  have hx200 : Bounds (-285261127 / 20000000000) (-3565763837 / 250000000000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx199
  let x201 : ℝ := x183+x200
  have hx201 : Bounds (13577682473 / 20000000000) (169721031413 / 250000000000) x201 := by
    apply bounds_add hx183 hx200 <;> norm_num
  let x202 : ℝ := x183-x199
  have hx202 : Bounds (13577682473 / 20000000000) (169721031413 / 250000000000) x202 := by
    exact hx201
  let x203 : ℝ := biasE (84247 / 500000)
  have hx203 : Bounds (13577682473 / 20000000000) (169721031413 / 250000000000) x203 := by
    simpa +zetaDelta only [biasE, div_one] using hx202
  let x204 : ℝ := Real.log (2 / 1)
  have hx204 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x204 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x205 : ℝ := (1 / 1)+(84091 / 500000)
  have hx205 : Bounds (584091 / 500000) (584091 / 500000) x205 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((84091 / 500000) : ℝ)) <;> norm_num
  let x206 : ℝ := (1 / 1)+(84091 / 500000)
  have hx206 : Bounds (584091 / 500000) (584091 / 500000) x206 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((84091 / 500000) : ℝ)) <;> norm_num
  let x207 : ℝ := Real.log x206
  have hx207 : Bounds (77724347 / 500000000) (31089739 / 200000000) x207 := by
    exact bounds_log hx206 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x208 : ℝ := x205*x207
  have hx208 : Bounds (90796183127 / 500000000000) (181592367423 / 1000000000000) x208 := by
    apply bounds_mul hx205 hx207 <;> norm_num
  let x209 : ℝ := -(84091 / 500000)
  have hx209 : Bounds (-84091 / 500000) (-84091 / 500000) x209 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((84091 / 500000) : ℝ))
  let x210 : ℝ := (1 / 1)+x209
  have hx210 : Bounds (415909 / 500000) (415909 / 500000) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx209 <;> norm_num
  let x211 : ℝ := (1 / 1)-(84091 / 500000)
  have hx211 : Bounds (415909 / 500000) (415909 / 500000) x211 := by
    exact hx210
  let x212 : ℝ := -(84091 / 500000)
  have hx212 : Bounds (-84091 / 500000) (-84091 / 500000) x212 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((84091 / 500000) : ℝ))
  let x213 : ℝ := (1 / 1)+x212
  have hx213 : Bounds (415909 / 500000) (415909 / 500000) x213 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx212 <;> norm_num
  let x214 : ℝ := (1 / 1)-(84091 / 500000)
  have hx214 : Bounds (415909 / 500000) (415909 / 500000) x214 := by
    exact hx213
  let x215 : ℝ := Real.log x214
  have hx215 : Bounds (-184141613 / 1000000000) (-46035403 / 250000000) x215 := by
    exact bounds_log hx214 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x216 : ℝ := x211*x215
  have hx216 : Bounds (-153172308243 / 1000000000000) (-15317230741 / 100000000000) x216 := by
    apply bounds_mul hx211 hx215 <;> norm_num
  let x217 : ℝ := x208+x216
  have hx217 : Bounds (28420058011 / 1000000000000) (28420060013 / 1000000000000) x217 := by
    apply bounds_add hx208 hx216 <;> norm_num
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (2842005801 / 200000000000) (14210030007 / 1000000000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (2842005801 / 200000000000) (14210030007 / 1000000000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := -x220
  have hx221 : Bounds (-14210030007 / 1000000000000) (-2842005801 / 200000000000) x221 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx220
  let x222 : ℝ := x204+x221
  have hx222 : Bounds (678937149993 / 1000000000000) (135787430399 / 200000000000) x222 := by
    apply bounds_add hx204 hx221 <;> norm_num
  let x223 : ℝ := x204-x220
  have hx223 : Bounds (678937149993 / 1000000000000) (135787430399 / 200000000000) x223 := by
    exact hx222
  let x224 : ℝ := biasE (84091 / 500000)
  have hx224 : Bounds (678937149993 / 1000000000000) (135787430399 / 200000000000) x224 := by
    simpa +zetaDelta only [biasE, div_one] using hx223
  let x225 : ℝ := biasE c
  have hx225 : Bounds (13577682473 / 20000000000) (135787430399 / 200000000000) x225 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx203.1 hx224.2
  let x226 : ℝ := x159⁻¹
  have hx226 : Bounds (209112416493 / 50000000000) (1047513737771 / 250000000000) x226 := by
    apply bounds_inv hx159 <;> norm_num
  let x227 : ℝ := x148*x226
  have hx227 : Bounds (716163194717 / 500000000000) (1437755090153 / 1000000000000) x227 := by
    apply bounds_mul hx148 hx226 <;> norm_num
  let x228 : ℝ := x148/x159
  have hx228 : Bounds (716163194717 / 500000000000) (1437755090153 / 1000000000000) x228 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx227
  let x229 : ℝ := c*x148
  have hx229 : Bounds (359991053 / 6250000000) (11563242439 / 200000000000) x229 := by
    apply bounds_mul hc hx148 <;> norm_num
  let x230 : ℝ := x225+x229
  have hx230 : Bounds (73648269213 / 100000000000) (73675336419 / 100000000000) x230 := by
    apply bounds_add hx225 hx229 <;> norm_num
  let x231 : ℝ := x*x170
  have hx231 : Bounds (3498708719 / 125000000000) (438944371 / 15625000000) x231 := by
    apply bounds_mul hx hx170 <;> norm_num
  let x232 : ℝ := x48+x231
  have hx232 : Bounds (173336987869 / 250000000000) (138710230909 / 200000000000) x232 := by
    apply bounds_add hx48 hx231 <;> norm_num
  let x233 : ℝ := x232⁻¹
  have hx233 : Bounds (36046367793 / 25000000000) (90142330221 / 62500000000) x233 := by
    apply bounds_inv hx232 <;> norm_num
  let x234 : ℝ := x230*x233
  have hx234 : Bounds (1061901039747 / 1000000000000) (53130132037 / 50000000000) x234 := by
    apply bounds_mul hx230 hx233 <;> norm_num
  let x235 : ℝ := x230/x232
  have hx235 : Bounds (1061901039747 / 1000000000000) (53130132037 / 50000000000) x235 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx234
  let x236 : ℝ := y*y
  have hx236 : Bounds (548636929 / 10000000000) (55061091801 / 1000000000000) x236 := by
    apply bounds_mul hy hy <;> norm_num
  let x237 : ℝ := -x236
  have hx237 : Bounds (-55061091801 / 1000000000000) (-548636929 / 10000000000) x237 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx236
  let x238 : ℝ := (1 / 1)+x237
  have hx238 : Bounds (944938908199 / 1000000000000) (9451363071 / 10000000000) x238 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx237 <;> norm_num
  let x239 : ℝ := (1 / 1)-x236
  have hx239 : Bounds (944938908199 / 1000000000000) (9451363071 / 10000000000) x239 := by
    exact hx238
  let x240 : ℝ := x239*x159
  have hx240 : Bounds (225519454811 / 1000000000000) (110345513 / 488281250) x240 := by
    apply bounds_mul hx239 hx159 <;> norm_num
  let x241 : ℝ := c*c
  have hx241 : Bounds (7071296281 / 250000000000) (7097557009 / 250000000000) x241 := by
    apply bounds_mul hc hc <;> norm_num
  let x242 : ℝ := -x241
  have hx242 : Bounds (-7097557009 / 250000000000) (-7071296281 / 250000000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx241
  let x243 : ℝ := (1 / 1)+x242
  have hx243 : Bounds (242902442991 / 250000000000) (242928703719 / 250000000000) x243 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx242 <;> norm_num
  let x244 : ℝ := (1 / 1)-x241
  have hx244 : Bounds (242902442991 / 250000000000) (242928703719 / 250000000000) x244 := by
    exact hx243
  let x245 : ℝ := x244*x182
  have hx245 : Bounds (21481491649 / 31250000000) (343767288003 / 500000000000) x245 := by
    apply bounds_mul hx244 hx182 <;> norm_num
  let x246 : ℝ := y*y
  have hx246 : Bounds (548636929 / 10000000000) (55061091801 / 1000000000000) x246 := by
    apply bounds_mul hy hy <;> norm_num
  let x247 : ℝ := (1 / 1)+x246
  have hx247 : Bounds (10548636929 / 10000000000) (1055061091801 / 1000000000000) x247 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx246 <;> norm_num
  let x248 : ℝ := x247*x159
  have hx248 : Bounds (15734633931 / 62500000000) (252271268607 / 1000000000000) x248 := by
    apply bounds_mul hx247 hx159 <;> norm_num
  let x249 : ℝ := -y
  have hx249 : Bounds (-234651 / 1000000) (-23423 / 100000) x249 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x250 : ℝ := x248+x249
  have hx250 : Bounds (1068946431 / 62500000000) (18041268607 / 1000000000000) x250 := by
    apply bounds_add hx248 hx249 <;> norm_num
  let x251 : ℝ := x248-y
  have hx251 : Bounds (1068946431 / 62500000000) (18041268607 / 1000000000000) x251 := by
    exact hx250
  let x252 : ℝ := x240*x240
  have hx252 : Bounds (25429512249 / 500000000000) (12767600039 / 250000000000) x252 := by
    apply bounds_mul hx240 hx240 <;> norm_num
  let x253 : ℝ := x252⁻¹
  have hx253 : Bounds (19580813875461 / 1000000000000) (1966219387553 / 100000000000) x253 := by
    apply bounds_inv hx252 <;> norm_num
  let x254 : ℝ := x251*x253
  have hx254 : Bounds (334893457731 / 1000000000000) (44341365139 / 125000000000) x254 := by
    apply bounds_mul hx251 hx253 <;> norm_num
  let x255 : ℝ := x251/x252
  have hx255 : Bounds (334893457731 / 1000000000000) (44341365139 / 125000000000) x255 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx254
  let x256 : ℝ := (-2 / 1)*x255
  have hx256 : Bounds (-44341365139 / 62500000000) (-334893457731 / 500000000000) x256 := by
    apply bounds_mul (bounds_const ((-2 / 1) : ℝ)) hx255 <;> norm_num
  let x257 : ℝ := x256*x228
  have hx257 : Bounds (-1020032374927 / 1000000000000) (-959353474313 / 1000000000000) x257 := by
    apply bounds_mul hx256 hx228 <;> norm_num
  let x258 : ℝ := (2 / 1)*x182
  have hx258 : Bounds (1414987277 / 1000000000) (1415095387 / 1000000000) x258 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx182 <;> norm_num
  let x259 : ℝ := c*c
  have hx259 : Bounds (7071296281 / 250000000000) (7097557009 / 250000000000) x259 := by
    apply bounds_mul hc hc <;> norm_num
  let x260 : ℝ := -x259
  have hx260 : Bounds (-7097557009 / 250000000000) (-7071296281 / 250000000000) x260 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx259
  let x261 : ℝ := x258+x260
  have hx261 : Bounds (346649262241 / 250000000000) (346702550469 / 250000000000) x261 := by
    apply bounds_add hx258 hx260 <;> norm_num
  let x262 : ℝ := x258-x259
  have hx262 : Bounds (346649262241 / 250000000000) (346702550469 / 250000000000) x262 := by
    exact hx261
  let x263 : ℝ := c*x262
  have hx263 : Bounds (29150083111 / 125000000000) (46733839631 / 200000000000) x263 := by
    apply bounds_mul hc hx262 <;> norm_num
  let x264 : ℝ := x245*x245
  have hx264 : Bounds (472529391069 / 1000000000000) (118175948301 / 250000000000) x264 := by
    apply bounds_mul hx245 hx245 <;> norm_num
  let x265 : ℝ := x264⁻¹
  have hx265 : Bounds (528872421999 / 250000000000) (264533809669 / 125000000000) x265 := by
    apply bounds_inv hx264 <;> norm_num
  let x266 : ℝ := x263*x265
  have hx266 : Bounds (123333400451 / 250000000000) (247253612761 / 500000000000) x266 := by
    apply bounds_mul hx263 hx265 <;> norm_num
  let x267 : ℝ := x263/x264
  have hx267 : Bounds (123333400451 / 250000000000) (247253612761 / 500000000000) x267 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx266
  let x268 : ℝ := (2 / 1)*x267
  have hx268 : Bounds (123333400451 / 125000000000) (247253612761 / 250000000000) x268 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx267 <;> norm_num
  let x269 : ℝ := x268*x235
  have hx269 : Bounds (209548585879 / 200000000000) (105092936741 / 100000000000) x269 := by
    apply bounds_mul hx268 hx235 <;> norm_num
  let x270 : ℝ := x257+x269
  have hx270 : Bounds (6927638617 / 250000000000) (91575893097 / 1000000000000) x270 := by
    apply bounds_add hx257 hx269 <;> norm_num
  have hPos : 0 < x270 :=
    lt_of_lt_of_le (by norm_num) hx270.1
  have hBridgeL : doubleCapBridgeL x = x48 := by
    exact hEll'
  rw [← doubleCapBridgeDerivativeTraceForm_eq x]
  simpa +zetaDelta only [doubleCapBridgeDerivativeTraceForm,
    hBridgeL, SmallMean.A, biasB, div_one, pow_two] using hPos

theorem acceptedCell : DoubleCapBridgeDerivativeCellCertificate
    (⟨136, by decide⟩ : Fin 256) doubleCapBridgeDerivativeExpression where
  positive x hx := by
    have hloEq : doubleCapBridgeLo (⟨136, by decide⟩ : Fin 256) =
        (211 / 1280) := by norm_num [doubleCapBridgeLo, doubleCapBridgeStep]
    have hhiEq : doubleCapBridgeHi (⟨136, by decide⟩ : Fin 256) =
        (1691 / 10240) := by norm_num [doubleCapBridgeHi, doubleCapBridgeStep]
    have hlo : (211 / 1280) ≤ x := by
      simpa only [hloEq] using hx.1
    have hhi : x ≤ (1691 / 10240) := by
      simpa only [hhiEq] using hx.2
    exact cell_derivative_pos x ⟨hlo, hhi⟩

#print axioms cell_derivative_pos
#print axioms acceptedCell

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell136

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell137 =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell137
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_derivative_pos (x : ℝ)
    (hx : Bounds (1691 / 10240) (847 / 5120) x) :
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
  have hx0 : Bounds (1691 / 5120) (847 / 2560) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx <;> norm_num
  let x1 : ℝ := Real.log (2 / 1)
  have hx1 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x1 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x2 : ℝ := Real.log (2 / 1)
  have hx2 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x2 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x3 : ℝ := (1 / 1)+(847 / 2560)
  have hx3 : Bounds (3407 / 2560) (3407 / 2560) x3 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((847 / 2560) : ℝ)) <;> norm_num
  let x4 : ℝ := (1 / 1)+(847 / 2560)
  have hx4 : Bounds (3407 / 2560) (3407 / 2560) x4 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((847 / 2560) : ℝ)) <;> norm_num
  let x5 : ℝ := Real.log x4
  have hx5 : Bounds (3572811 / 12500000) (285824881 / 1000000000) x5 := by
    exact bounds_log hx4 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x6 : ℝ := x3*x5
  have hx6 : Bounds (95098180289 / 250000000000) (47549090311 / 125000000000) x6 := by
    apply bounds_mul hx3 hx5 <;> norm_num
  let x7 : ℝ := -(847 / 2560)
  have hx7 : Bounds (-847 / 2560) (-847 / 2560) x7 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((847 / 2560) : ℝ))
  let x8 : ℝ := (1 / 1)+x7
  have hx8 : Bounds (1713 / 2560) (1713 / 2560) x8 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx7 <;> norm_num
  let x9 : ℝ := (1 / 1)-(847 / 2560)
  have hx9 : Bounds (1713 / 2560) (1713 / 2560) x9 := by
    exact hx8
  let x10 : ℝ := -(847 / 2560)
  have hx10 : Bounds (-847 / 2560) (-847 / 2560) x10 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((847 / 2560) : ℝ))
  let x11 : ℝ := (1 / 1)+x10
  have hx11 : Bounds (1713 / 2560) (1713 / 2560) x11 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx10 <;> norm_num
  let x12 : ℝ := (1 / 1)-(847 / 2560)
  have hx12 : Bounds (1713 / 2560) (1713 / 2560) x12 := by
    exact hx11
  let x13 : ℝ := Real.log x12
  have hx13 : Bounds (-5022013 / 12500000) (-401761039 / 1000000000) x13 := by
    exact bounds_log hx12 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x14 : ℝ := x9*x13
  have hx14 : Bounds (-268834633407 / 1000000000000) (-268834632737 / 1000000000000) x14 := by
    apply bounds_mul hx9 hx13 <;> norm_num
  let x15 : ℝ := x6+x14
  have hx15 : Bounds (111558087749 / 1000000000000) (111558089751 / 1000000000000) x15 := by
    apply bounds_add hx6 hx14 <;> norm_num
  let x16 : ℝ := (2 / 1)⁻¹
  have hx16 : Bounds (1 / 2) (1 / 2) x16 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x17 : ℝ := x15*x16
  have hx17 : Bounds (27889521937 / 500000000000) (13944761219 / 250000000000) x17 := by
    apply bounds_mul hx15 hx16 <;> norm_num
  let x18 : ℝ := x15/(2 / 1)
  have hx18 : Bounds (27889521937 / 500000000000) (13944761219 / 250000000000) x18 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx17
  let x19 : ℝ := -x18
  have hx19 : Bounds (-13944761219 / 250000000000) (-27889521937 / 500000000000) x19 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx18
  let x20 : ℝ := x2+x19
  have hx20 : Bounds (159342033781 / 250000000000) (318684068563 / 500000000000) x20 := by
    apply bounds_add hx2 hx19 <;> norm_num
  let x21 : ℝ := x2-x18
  have hx21 : Bounds (159342033781 / 250000000000) (318684068563 / 500000000000) x21 := by
    exact hx20
  let x22 : ℝ := biasE (847 / 2560)
  have hx22 : Bounds (159342033781 / 250000000000) (318684068563 / 500000000000) x22 := by
    simpa +zetaDelta only [biasE, div_one] using hx21
  let x23 : ℝ := Real.log (2 / 1)
  have hx23 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x23 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x24 : ℝ := (1 / 1)+(1691 / 5120)
  have hx24 : Bounds (6811 / 5120) (6811 / 5120) x24 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1691 / 5120) : ℝ)) <;> norm_num
  let x25 : ℝ := (1 / 1)+(1691 / 5120)
  have hx25 : Bounds (6811 / 5120) (6811 / 5120) x25 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1691 / 5120) : ℝ)) <;> norm_num
  let x26 : ℝ := Real.log x25
  have hx26 : Bounds (285384513 / 1000000000) (142692257 / 500000000) x26 := by
    exact bounds_log hx25 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x27 : ℝ := x24*x26
  have hx27 : Bounds (379639437117 / 1000000000000) (379639438449 / 1000000000000) x27 := by
    apply bounds_mul hx24 hx26 <;> norm_num
  let x28 : ℝ := -(1691 / 5120)
  have hx28 : Bounds (-1691 / 5120) (-1691 / 5120) x28 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1691 / 5120) : ℝ))
  let x29 : ℝ := (1 / 1)+x28
  have hx29 : Bounds (3429 / 5120) (3429 / 5120) x29 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx28 <;> norm_num
  let x30 : ℝ := (1 / 1)-(1691 / 5120)
  have hx30 : Bounds (3429 / 5120) (3429 / 5120) x30 := by
    exact hx29
  let x31 : ℝ := -(1691 / 5120)
  have hx31 : Bounds (-1691 / 5120) (-1691 / 5120) x31 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1691 / 5120) : ℝ))
  let x32 : ℝ := (1 / 1)+x31
  have hx32 : Bounds (3429 / 5120) (3429 / 5120) x32 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx31 <;> norm_num
  let x33 : ℝ := (1 / 1)-(1691 / 5120)
  have hx33 : Bounds (3429 / 5120) (3429 / 5120) x33 := by
    exact hx32
  let x34 : ℝ := Real.log x33
  have hx34 : Bounds (-200442883 / 500000000) (-80177153 / 200000000) x34 := by
    exact bounds_log hx33 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x35 : ℝ := x30*x34
  have hx35 : Bounds (-268483846019 / 1000000000000) (-67120961337 / 250000000000) x35 := by
    apply bounds_mul hx30 hx34 <;> norm_num
  let x36 : ℝ := x27+x35
  have hx36 : Bounds (55577795549 / 500000000000) (111155593101 / 1000000000000) x36 := by
    apply bounds_add hx27 hx35 <;> norm_num
  let x37 : ℝ := (2 / 1)⁻¹
  have hx37 : Bounds (1 / 2) (1 / 2) x37 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x38 : ℝ := x36*x37
  have hx38 : Bounds (55577795549 / 1000000000000) (55577796551 / 1000000000000) x38 := by
    apply bounds_mul hx36 hx37 <;> norm_num
  let x39 : ℝ := x36/(2 / 1)
  have hx39 : Bounds (55577795549 / 1000000000000) (55577796551 / 1000000000000) x39 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx38
  let x40 : ℝ := -x39
  have hx40 : Bounds (-55577796551 / 1000000000000) (-55577795549 / 1000000000000) x40 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx39
  let x41 : ℝ := x23+x40
  have hx41 : Bounds (637569383449 / 1000000000000) (637569385451 / 1000000000000) x41 := by
    apply bounds_add hx23 hx40 <;> norm_num
  let x42 : ℝ := x23-x39
  have hx42 : Bounds (637569383449 / 1000000000000) (637569385451 / 1000000000000) x42 := by
    exact hx41
  let x43 : ℝ := biasE (1691 / 5120)
  have hx43 : Bounds (637569383449 / 1000000000000) (637569385451 / 1000000000000) x43 := by
    simpa +zetaDelta only [biasE, div_one] using hx42
  let x44 : ℝ := biasE x0
  have hx44 : Bounds (159342033781 / 250000000000) (637569385451 / 1000000000000) x44 := by
    exact bounds_biasE hx0 (by norm_num) (by norm_num) hx22.1 hx43.2
  let x45 : ℝ := x1+x44
  have hx45 : Bounds (332628828781 / 250000000000) (1330716566451 / 1000000000000) x45 := by
    apply bounds_add hx1 hx44 <;> norm_num
  let x46 : ℝ := (2 / 1)⁻¹
  have hx46 : Bounds (1 / 2) (1 / 2) x46 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x47 : ℝ := x45*x46
  have hx47 : Bounds (332628828781 / 500000000000) (332679141613 / 500000000000) x47 := by
    apply bounds_mul hx45 hx46 <;> norm_num
  let x48 : ℝ := x45/(2 / 1)
  have hx48 : Bounds (332628828781 / 500000000000) (332679141613 / 500000000000) x48 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx47
  let x49 : ℝ := Real.log (2 / 1)
  have hx49 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x49 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x50 : ℝ := (1 / 1)+(4693 / 20000)
  have hx50 : Bounds (24693 / 20000) (24693 / 20000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((4693 / 20000) : ℝ)) <;> norm_num
  let x51 : ℝ := (1 / 1)+(4693 / 20000)
  have hx51 : Bounds (24693 / 20000) (24693 / 20000) x51 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((4693 / 20000) : ℝ)) <;> norm_num
  let x52 : ℝ := Real.log x51
  have hx52 : Bounds (210787529 / 1000000000) (21078753 / 100000000) x52 := by
    exact bounds_log hx51 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x53 : ℝ := x50*x52
  have hx53 : Bounds (260248822679 / 1000000000000) (52049764783 / 200000000000) x53 := by
    apply bounds_mul hx50 hx52 <;> norm_num
  let x54 : ℝ := -(4693 / 20000)
  have hx54 : Bounds (-4693 / 20000) (-4693 / 20000) x54 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((4693 / 20000) : ℝ))
  let x55 : ℝ := (1 / 1)+x54
  have hx55 : Bounds (15307 / 20000) (15307 / 20000) x55 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx54 <;> norm_num
  let x56 : ℝ := (1 / 1)-(4693 / 20000)
  have hx56 : Bounds (15307 / 20000) (15307 / 20000) x56 := by
    exact hx55
  let x57 : ℝ := -(4693 / 20000)
  have hx57 : Bounds (-4693 / 20000) (-4693 / 20000) x57 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((4693 / 20000) : ℝ))
  let x58 : ℝ := (1 / 1)+x57
  have hx58 : Bounds (15307 / 20000) (15307 / 20000) x58 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx57 <;> norm_num
  let x59 : ℝ := (1 / 1)-(4693 / 20000)
  have hx59 : Bounds (15307 / 20000) (15307 / 20000) x59 := by
    exact hx58
  let x60 : ℝ := Real.log x59
  have hx60 : Bounds (-133711017 / 500000000) (-267422033 / 1000000000) x60 := by
    exact bounds_log hx59 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x61 : ℝ := x56*x60
  have hx61 : Bounds (-102335726861 / 500000000000) (-51167863239 / 250000000000) x61 := by
    apply bounds_mul hx56 hx60 <;> norm_num
  let x62 : ℝ := x53+x61
  have hx62 : Bounds (55577368957 / 1000000000000) (55577370959 / 1000000000000) x62 := by
    apply bounds_add hx53 hx61 <;> norm_num
  let x63 : ℝ := (2 / 1)⁻¹
  have hx63 : Bounds (1 / 2) (1 / 2) x63 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x64 : ℝ := x62*x63
  have hx64 : Bounds (13894342239 / 500000000000) (694717137 / 25000000000) x64 := by
    apply bounds_mul hx62 hx63 <;> norm_num
  let x65 : ℝ := x62/(2 / 1)
  have hx65 : Bounds (13894342239 / 500000000000) (694717137 / 25000000000) x65 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx64
  let x66 : ℝ := -x65
  have hx66 : Bounds (-694717137 / 25000000000) (-13894342239 / 500000000000) x66 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx65
  let x67 : ℝ := x49+x66
  have hx67 : Bounds (16633962363 / 25000000000) (332679248261 / 500000000000) x67 := by
    apply bounds_add hx49 hx66 <;> norm_num
  let x68 : ℝ := x49-x65
  have hx68 : Bounds (16633962363 / 25000000000) (332679248261 / 500000000000) x68 := by
    exact hx67
  let x69 : ℝ := biasE (4693 / 20000)
  have hx69 : Bounds (16633962363 / 25000000000) (332679248261 / 500000000000) x69 := by
    simpa +zetaDelta only [biasE, div_one] using hx68
  let x70 : ℝ := Real.log (2 / 1)
  have hx70 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x70 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x71 : ℝ := (1 / 1)+(3673 / 15625)
  have hx71 : Bounds (19298 / 15625) (19298 / 15625) x71 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((3673 / 15625) : ℝ)) <;> norm_num
  let x72 : ℝ := (1 / 1)+(3673 / 15625)
  have hx72 : Bounds (19298 / 15625) (19298 / 15625) x72 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((3673 / 15625) : ℝ)) <;> norm_num
  let x73 : ℝ := Real.log x72
  have hx73 : Bounds (211129267 / 1000000000) (52782317 / 250000000) x73 := by
    exact bounds_log hx72 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x74 : ℝ := x71*x73
  have hx74 : Bounds (65189961513 / 250000000000) (32594980911 / 125000000000) x74 := by
    apply bounds_mul hx71 hx73 <;> norm_num
  let x75 : ℝ := -(3673 / 15625)
  have hx75 : Bounds (-3673 / 15625) (-3673 / 15625) x75 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((3673 / 15625) : ℝ))
  let x76 : ℝ := (1 / 1)+x75
  have hx76 : Bounds (11952 / 15625) (11952 / 15625) x76 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx75 <;> norm_num
  let x77 : ℝ := (1 / 1)-(3673 / 15625)
  have hx77 : Bounds (11952 / 15625) (11952 / 15625) x77 := by
    exact hx76
  let x78 : ℝ := -(3673 / 15625)
  have hx78 : Bounds (-3673 / 15625) (-3673 / 15625) x78 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((3673 / 15625) : ℝ))
  let x79 : ℝ := (1 / 1)+x78
  have hx79 : Bounds (11952 / 15625) (11952 / 15625) x79 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx78 <;> norm_num
  let x80 : ℝ := (1 / 1)-(3673 / 15625)
  have hx80 : Bounds (11952 / 15625) (11952 / 15625) x80 := by
    exact hx79
  let x81 : ℝ := Real.log x80
  have hx81 : Bounds (-4187087 / 15625000) (-267973567 / 1000000000) x81 := by
    exact bounds_log hx80 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x82 : ℝ := x77*x81
  have hx82 : Bounds (-12811280339 / 62500000000) (-102490242329 / 500000000000) x82 := by
    apply bounds_mul hx77 hx81 <;> norm_num
  let x83 : ℝ := x74+x82
  have hx83 : Bounds (13944840157 / 250000000000) (5577936263 / 100000000000) x83 := by
    apply bounds_add hx74 hx82 <;> norm_num
  let x84 : ℝ := (2 / 1)⁻¹
  have hx84 : Bounds (1 / 2) (1 / 2) x84 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x85 : ℝ := x83*x84
  have hx85 : Bounds (13944840157 / 500000000000) (5577936263 / 200000000000) x85 := by
    apply bounds_mul hx83 hx84 <;> norm_num
  let x86 : ℝ := x83/(2 / 1)
  have hx86 : Bounds (13944840157 / 500000000000) (5577936263 / 200000000000) x86 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx85
  let x87 : ℝ := -x86
  have hx87 : Bounds (-5577936263 / 200000000000) (-13944840157 / 500000000000) x87 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx86
  let x88 : ℝ := x70+x87
  have hx88 : Bounds (133051499737 / 200000000000) (332628750343 / 500000000000) x88 := by
    apply bounds_add hx70 hx87 <;> norm_num
  let x89 : ℝ := x70-x86
  have hx89 : Bounds (133051499737 / 200000000000) (332628750343 / 500000000000) x89 := by
    exact hx88
  let x90 : ℝ := biasE (3673 / 15625)
  have hx90 : Bounds (133051499737 / 200000000000) (332628750343 / 500000000000) x90 := by
    simpa +zetaDelta only [biasE, div_one] using hx89
  let y : ℝ := doubleCapHighTailY x
  have hEll' : Real.log 2 * doubleCapHighTailFloor x = x48 := by
    simpa +zetaDelta only [div_one] using hEll
  have hy : Bounds (4693 / 20000) (3673 / 15625) y := by
    dsimp only [y, doubleCapHighTailY]
    apply entropyInverseBias_bracket hh0.le hh1.le
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (3673 / 15625) ≤ (332628750343 / 500000000000) := hx90.2
      have h2 : (332628828781 / 500000000000) ≤ x48 := hx48.1
      linarith [hEll']
    · have h1 : x48 ≤ (332679141613 / 500000000000) := hx48.2
      have h2 : (16633962363 / 25000000000) ≤ biasE (4693 / 20000) := hx69.1
      linarith [hEll']
  let x91 : ℝ := x⁻¹
  have hx91 : Bounds (3022432113341 / 500000000000) (3027794204613 / 500000000000) x91 := by
    apply bounds_inv hx <;> norm_num
  let x92 : ℝ := x48*x91
  have hx92 : Bounds (2010696107861 / 500000000000) (2014567953943 / 500000000000) x92 := by
    apply bounds_mul hx48 hx91 <;> norm_num
  let x93 : ℝ := x48/x
  have hx93 : Bounds (2010696107861 / 500000000000) (2014567953943 / 500000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(168493 / 1000000)
  have hx95 : Bounds (1168493 / 1000000) (1168493 / 1000000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((168493 / 1000000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(168493 / 1000000)
  have hx96 : Bounds (1168493 / 1000000) (1168493 / 1000000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((168493 / 1000000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (38928721 / 250000000) (31142977 / 200000000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (181951751949 / 1000000000000) (181951753119 / 1000000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(168493 / 1000000)
  have hx99 : Bounds (-168493 / 1000000) (-168493 / 1000000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((168493 / 1000000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (831507 / 1000000) (831507 / 1000000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(168493 / 1000000)
  have hx101 : Bounds (831507 / 1000000) (831507 / 1000000) x101 := by
    exact hx100
  let x102 : ℝ := -(168493 / 1000000)
  have hx102 : Bounds (-168493 / 1000000) (-168493 / 1000000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((168493 / 1000000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (831507 / 1000000) (831507 / 1000000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(168493 / 1000000)
  have hx104 : Bounds (831507 / 1000000) (831507 / 1000000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-92257781 / 500000000) (-184515561 / 1000000000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-38356495353 / 250000000000) (-7671299029 / 50000000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (28525770537 / 1000000000000) (28525772539 / 1000000000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (3565721317 / 250000000000) (1426288627 / 100000000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (3565721317 / 250000000000) (1426288627 / 100000000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-1426288627 / 100000000000) (-3565721317 / 250000000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (67888429373 / 100000000000) (169721073933 / 250000000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (67888429373 / 100000000000) (169721073933 / 250000000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (168493 / 1000000)
  have hx114 : Bounds (67888429373 / 100000000000) (169721073933 / 250000000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(84403 / 500000)
  have hx116 : Bounds (584403 / 500000) (584403 / 500000) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((84403 / 500000) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(84403 / 500000)
  have hx117 : Bounds (584403 / 500000) (584403 / 500000) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((84403 / 500000) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (77991357 / 500000000) (31196543 / 200000000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (182313532019 / 1000000000000) (182313533189 / 1000000000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(84403 / 500000)
  have hx120 : Bounds (-84403 / 500000) (-84403 / 500000) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((84403 / 500000) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (415597 / 500000) (415597 / 500000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(84403 / 500000)
  have hx122 : Bounds (415597 / 500000) (415597 / 500000) x122 := by
    exact hx121
  let x123 : ℝ := -(84403 / 500000)
  have hx123 : Bounds (-84403 / 500000) (-84403 / 500000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((84403 / 500000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (415597 / 500000) (415597 / 500000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(84403 / 500000)
  have hx125 : Bounds (415597 / 500000) (415597 / 500000) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-92446029 / 500000000) (-184892057 / 1000000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-76840584629 / 500000000000) (-76840584213 / 500000000000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (28632362761 / 1000000000000) (28632364763 / 1000000000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (715809069 / 50000000000) (7158091191 / 500000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (715809069 / 50000000000) (7158091191 / 500000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-7158091191 / 500000000000) (-715809069 / 50000000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (339415498809 / 500000000000) (33941549981 / 50000000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (339415498809 / 500000000000) (33941549981 / 50000000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (84403 / 500000)
  have hx135 : Bounds (339415498809 / 500000000000) (33941549981 / 50000000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(168493 / 1000000)
  have hx136 : Bounds (677576438603 / 1000000000000) (42430074783 / 62500000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((168493 / 1000000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(84403 / 500000)
  have hx137 : Bounds (678835134367 / 1000000000000) (680142316067 / 1000000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((84403 / 500000) : ℝ)) <;> norm_num
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
  have hc : Bounds (168493 / 1000000) (84403 / 500000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num)
      (by norm_num) (show 0 < x93 by linarith [hx93.1]) hcEq
    · have h1 : x93 * (168493 / 1000000) ≤ (42430074783 / 62500000000) := hx136.2
      have h2 : (67888429373 / 100000000000) ≤ biasE (168493 / 1000000) := hx114.1
      linarith
    · have h1 : biasE (84403 / 500000) ≤ (33941549981 / 50000000000) := hx135.2
      have h2 : (678835134367 / 1000000000000) ≤ x93 * (84403 / 500000) := hx137.1
      linarith
  let x138 : ℝ := (1 / 1)+x0
  have hx138 : Bounds (6811 / 5120) (3407 / 2560) x138 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx0 <;> norm_num
  let x139 : ℝ := -x0
  have hx139 : Bounds (-847 / 2560) (-1691 / 5120) x139 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x140 : ℝ := (1 / 1)+x139
  have hx140 : Bounds (1713 / 2560) (3429 / 5120) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx139 <;> norm_num
  let x141 : ℝ := (1 / 1)-x0
  have hx141 : Bounds (1713 / 2560) (3429 / 5120) x141 := by
    exact hx140
  let x142 : ℝ := x141⁻¹
  have hx142 : Bounds (1493146689997 / 1000000000000) (373613543491 / 250000000000) x142 := by
    apply bounds_inv hx141 <;> norm_num
  let x143 : ℝ := x138*x142
  have hx143 : Bounds (993146689997 / 500000000000) (248613543491 / 125000000000) x143 := by
    apply bounds_mul hx138 hx142 <;> norm_num
  let x144 : ℝ := x138/x141
  have hx144 : Bounds (993146689997 / 500000000000) (248613543491 / 125000000000) x144 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx143
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (343135139 / 500000000) (1074353 / 1562500) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_14.2)
  let x146 : ℝ := (2 / 1)⁻¹
  have hx146 : Bounds (1 / 2) (1 / 2) x146 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x147 : ℝ := x145*x146
  have hx147 : Bounds (343135139 / 1000000000) (1074353 / 3125000) x147 := by
    apply bounds_mul hx145 hx146 <;> norm_num
  let x148 : ℝ := x145/(2 / 1)
  have hx148 : Bounds (343135139 / 1000000000) (1074353 / 3125000) x148 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx147
  let x149 : ℝ := (1 / 1)+y
  have hx149 : Bounds (24693 / 20000) (19298 / 15625) x149 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x150 : ℝ := -y
  have hx150 : Bounds (-3673 / 15625) (-4693 / 20000) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (11952 / 15625) (15307 / 20000) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-y
  have hx152 : Bounds (11952 / 15625) (15307 / 20000) x152 := by
    exact hx151
  let x153 : ℝ := x152⁻¹
  have hx153 : Bounds (653295877703 / 500000000000) (1307312583669 / 1000000000000) x153 := by
    apply bounds_inv hx152 <;> norm_num
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (403295877703 / 250000000000) (807312583669 / 500000000000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x149/x152
  have hx155 : Bounds (403295877703 / 250000000000) (807312583669 / 500000000000) x155 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx154
  let x156 : ℝ := Real.log x155
  have hx156 : Bounds (239104781 / 500000000) (119775709 / 250000000) x156 := by
    exact bounds_log hx155 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_16.2)
  let x157 : ℝ := (2 / 1)⁻¹
  have hx157 : Bounds (1 / 2) (1 / 2) x157 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x158 : ℝ := x156*x157
  have hx158 : Bounds (239104781 / 1000000000) (119775709 / 500000000) x158 := by
    apply bounds_mul hx156 hx157 <;> norm_num
  let x159 : ℝ := x156/(2 / 1)
  have hx159 : Bounds (239104781 / 1000000000) (119775709 / 500000000) x159 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx158
  let x160 : ℝ := (1 / 1)+c
  have hx160 : Bounds (1168493 / 1000000) (584403 / 500000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x161 : ℝ := -c
  have hx161 : Bounds (-84403 / 500000) (-168493 / 1000000) x161 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x162 : ℝ := (1 / 1)+x161
  have hx162 : Bounds (415597 / 500000) (831507 / 1000000) x162 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx161 <;> norm_num
  let x163 : ℝ := (1 / 1)-c
  have hx163 : Bounds (415597 / 500000) (831507 / 1000000) x163 := by
    exact hx162
  let x164 : ℝ := x163⁻¹
  have hx164 : Bounds (150329462049 / 125000000000) (48123542759 / 40000000000) x164 := by
    apply bounds_inv hx163 <;> norm_num
  let x165 : ℝ := x160*x164
  have hx165 : Bounds (87829462049 / 62500000000) (28123542759 / 20000000000) x165 := by
    apply bounds_mul hx160 hx164 <;> norm_num
  let x166 : ℝ := x160/x163
  have hx166 : Bounds (87829462049 / 62500000000) (28123542759 / 20000000000) x166 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx165
  let x167 : ℝ := Real.log x166
  have hx167 : Bounds (170115223 / 500000000) (340874773 / 1000000000) x167 := by
    exact bounds_log hx166 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x168 : ℝ := (2 / 1)⁻¹
  have hx168 : Bounds (1 / 2) (1 / 2) x168 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x169 : ℝ := x167*x168
  have hx169 : Bounds (170115223 / 1000000000) (340874773 / 2000000000) x169 := by
    apply bounds_mul hx167 hx168 <;> norm_num
  let x170 : ℝ := x167/(2 / 1)
  have hx170 : Bounds (170115223 / 1000000000) (340874773 / 2000000000) x170 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx169
  let x171 : ℝ := Real.log (2 / 1)
  have hx171 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x171 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x172 : ℝ := c*c
  have hx172 : Bounds (28389891049 / 1000000000000) (7123866409 / 250000000000) x172 := by
    apply bounds_mul hc hc <;> norm_num
  let x173 : ℝ := -x172
  have hx173 : Bounds (-7123866409 / 250000000000) (-28389891049 / 1000000000000) x173 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx172
  let x174 : ℝ := (1 / 1)+x173
  have hx174 : Bounds (242876133591 / 250000000000) (971610108951 / 1000000000000) x174 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx173 <;> norm_num
  let x175 : ℝ := (1 / 1)-x172
  have hx175 : Bounds (242876133591 / 250000000000) (971610108951 / 1000000000000) x175 := by
    exact hx174
  let x176 : ℝ := Real.log x175
  have hx176 : Bounds (-28909343 / 1000000000) (-28800677 / 1000000000) x176 := by
    exact bounds_log hx175 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (-28909343 / 2000000000) (-28800677 / 2000000000) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (-28909343 / 2000000000) (-28800677 / 2000000000) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (28800677 / 2000000000) (28909343 / 2000000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x171+x180
  have hx181 : Bounds (1415095037 / 2000000000) (283040741 / 400000000) x181 := by
    apply bounds_add hx171 hx180 <;> norm_num
  let x182 : ℝ := x171-x179
  have hx182 : Bounds (1415095037 / 2000000000) (283040741 / 400000000) x182 := by
    exact hx181
  let x183 : ℝ := Real.log (2 / 1)
  have hx183 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x183 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x184 : ℝ := (1 / 1)+(84403 / 500000)
  have hx184 : Bounds (584403 / 500000) (584403 / 500000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((84403 / 500000) : ℝ)) <;> norm_num
  let x185 : ℝ := (1 / 1)+(84403 / 500000)
  have hx185 : Bounds (584403 / 500000) (584403 / 500000) x185 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((84403 / 500000) : ℝ)) <;> norm_num
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (77991357 / 500000000) (31196543 / 200000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x187 : ℝ := x184*x186
  have hx187 : Bounds (182313532019 / 1000000000000) (182313533189 / 1000000000000) x187 := by
    apply bounds_mul hx184 hx186 <;> norm_num
  let x188 : ℝ := -(84403 / 500000)
  have hx188 : Bounds (-84403 / 500000) (-84403 / 500000) x188 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((84403 / 500000) : ℝ))
  let x189 : ℝ := (1 / 1)+x188
  have hx189 : Bounds (415597 / 500000) (415597 / 500000) x189 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx188 <;> norm_num
  let x190 : ℝ := (1 / 1)-(84403 / 500000)
  have hx190 : Bounds (415597 / 500000) (415597 / 500000) x190 := by
    exact hx189
  let x191 : ℝ := -(84403 / 500000)
  have hx191 : Bounds (-84403 / 500000) (-84403 / 500000) x191 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((84403 / 500000) : ℝ))
  let x192 : ℝ := (1 / 1)+x191
  have hx192 : Bounds (415597 / 500000) (415597 / 500000) x192 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx191 <;> norm_num
  let x193 : ℝ := (1 / 1)-(84403 / 500000)
  have hx193 : Bounds (415597 / 500000) (415597 / 500000) x193 := by
    exact hx192
  let x194 : ℝ := Real.log x193
  have hx194 : Bounds (-92446029 / 500000000) (-184892057 / 1000000000) x194 := by
    exact bounds_log hx193 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x195 : ℝ := x190*x194
  have hx195 : Bounds (-76840584629 / 500000000000) (-76840584213 / 500000000000) x195 := by
    apply bounds_mul hx190 hx194 <;> norm_num
  let x196 : ℝ := x187+x195
  have hx196 : Bounds (28632362761 / 1000000000000) (28632364763 / 1000000000000) x196 := by
    apply bounds_add hx187 hx195 <;> norm_num
  let x197 : ℝ := (2 / 1)⁻¹
  have hx197 : Bounds (1 / 2) (1 / 2) x197 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x198 : ℝ := x196*x197
  have hx198 : Bounds (715809069 / 50000000000) (7158091191 / 500000000000) x198 := by
    apply bounds_mul hx196 hx197 <;> norm_num
  let x199 : ℝ := x196/(2 / 1)
  have hx199 : Bounds (715809069 / 50000000000) (7158091191 / 500000000000) x199 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx198
  let x200 : ℝ := -x199
  have hx200 : Bounds (-7158091191 / 500000000000) (-715809069 / 50000000000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx199
  let x201 : ℝ := x183+x200
  have hx201 : Bounds (339415498809 / 500000000000) (33941549981 / 50000000000) x201 := by
    apply bounds_add hx183 hx200 <;> norm_num
  let x202 : ℝ := x183-x199
  have hx202 : Bounds (339415498809 / 500000000000) (33941549981 / 50000000000) x202 := by
    exact hx201
  let x203 : ℝ := biasE (84403 / 500000)
  have hx203 : Bounds (339415498809 / 500000000000) (33941549981 / 50000000000) x203 := by
    simpa +zetaDelta only [biasE, div_one] using hx202
  let x204 : ℝ := Real.log (2 / 1)
  have hx204 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x204 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x205 : ℝ := (1 / 1)+(168493 / 1000000)
  have hx205 : Bounds (1168493 / 1000000) (1168493 / 1000000) x205 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((168493 / 1000000) : ℝ)) <;> norm_num
  let x206 : ℝ := (1 / 1)+(168493 / 1000000)
  have hx206 : Bounds (1168493 / 1000000) (1168493 / 1000000) x206 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((168493 / 1000000) : ℝ)) <;> norm_num
  let x207 : ℝ := Real.log x206
  have hx207 : Bounds (38928721 / 250000000) (31142977 / 200000000) x207 := by
    exact bounds_log hx206 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x208 : ℝ := x205*x207
  have hx208 : Bounds (181951751949 / 1000000000000) (181951753119 / 1000000000000) x208 := by
    apply bounds_mul hx205 hx207 <;> norm_num
  let x209 : ℝ := -(168493 / 1000000)
  have hx209 : Bounds (-168493 / 1000000) (-168493 / 1000000) x209 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((168493 / 1000000) : ℝ))
  let x210 : ℝ := (1 / 1)+x209
  have hx210 : Bounds (831507 / 1000000) (831507 / 1000000) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx209 <;> norm_num
  let x211 : ℝ := (1 / 1)-(168493 / 1000000)
  have hx211 : Bounds (831507 / 1000000) (831507 / 1000000) x211 := by
    exact hx210
  let x212 : ℝ := -(168493 / 1000000)
  have hx212 : Bounds (-168493 / 1000000) (-168493 / 1000000) x212 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((168493 / 1000000) : ℝ))
  let x213 : ℝ := (1 / 1)+x212
  have hx213 : Bounds (831507 / 1000000) (831507 / 1000000) x213 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx212 <;> norm_num
  let x214 : ℝ := (1 / 1)-(168493 / 1000000)
  have hx214 : Bounds (831507 / 1000000) (831507 / 1000000) x214 := by
    exact hx213
  let x215 : ℝ := Real.log x214
  have hx215 : Bounds (-92257781 / 500000000) (-184515561 / 1000000000) x215 := by
    exact bounds_log hx214 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x216 : ℝ := x211*x215
  have hx216 : Bounds (-38356495353 / 250000000000) (-7671299029 / 50000000000) x216 := by
    apply bounds_mul hx211 hx215 <;> norm_num
  let x217 : ℝ := x208+x216
  have hx217 : Bounds (28525770537 / 1000000000000) (28525772539 / 1000000000000) x217 := by
    apply bounds_add hx208 hx216 <;> norm_num
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (3565721317 / 250000000000) (1426288627 / 100000000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (3565721317 / 250000000000) (1426288627 / 100000000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := -x220
  have hx221 : Bounds (-1426288627 / 100000000000) (-3565721317 / 250000000000) x221 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx220
  let x222 : ℝ := x204+x221
  have hx222 : Bounds (67888429373 / 100000000000) (169721073933 / 250000000000) x222 := by
    apply bounds_add hx204 hx221 <;> norm_num
  let x223 : ℝ := x204-x220
  have hx223 : Bounds (67888429373 / 100000000000) (169721073933 / 250000000000) x223 := by
    exact hx222
  let x224 : ℝ := biasE (168493 / 1000000)
  have hx224 : Bounds (67888429373 / 100000000000) (169721073933 / 250000000000) x224 := by
    simpa +zetaDelta only [biasE, div_one] using hx223
  let x225 : ℝ := biasE c
  have hx225 : Bounds (339415498809 / 500000000000) (169721073933 / 250000000000) x225 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx203.1 hx224.2
  let x226 : ℝ := x159⁻¹
  have hx226 : Bounds (2087234566067 / 500000000000) (1338325393 / 320000000) x226 := by
    apply bounds_inv hx159 <;> norm_num
  let x227 : ℝ := x148*x226
  have hx227 : Bounds (716203522953 / 500000000000) (718916950473 / 500000000000) x227 := by
    apply bounds_mul hx148 hx226 <;> norm_num
  let x228 : ℝ := x148/x159
  have hx228 : Bounds (716203522953 / 500000000000) (718916950473 / 500000000000) x228 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx227
  let x229 : ℝ := c*x148
  have hx229 : Bounds (2312634759 / 40000000000) (29017157203 / 500000000000) x229 := by
    apply bounds_mul hc hx148 <;> norm_num
  let x230 : ℝ := x225+x229
  have hx230 : Bounds (736646866593 / 1000000000000) (368459305069 / 500000000000) x230 := by
    apply bounds_add hx225 hx229 <;> norm_num
  let x231 : ℝ := x*x170
  have hx231 : Bounds (5618453947 / 200000000000) (7048850897 / 250000000000) x231 := by
    apply bounds_mul hx hx170 <;> norm_num
  let x232 : ℝ := x48+x231
  have hx232 : Bounds (693349927297 / 1000000000000) (346776843407 / 500000000000) x232 := by
    apply bounds_add hx48 hx231 <;> norm_num
  let x233 : ℝ := x232⁻¹
  have hx233 : Bounds (1441849447291 / 1000000000000) (1442273173517 / 1000000000000) x233 := by
    apply bounds_inv hx232 <;> norm_num
  let x234 : ℝ := x230*x233
  have hx234 : Bounds (212426775489 / 200000000000) (265709485617 / 250000000000) x234 := by
    apply bounds_mul hx230 hx233 <;> norm_num
  let x235 : ℝ := x230/x232
  have hx235 : Bounds (212426775489 / 200000000000) (265709485617 / 250000000000) x235 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx234
  let x236 : ℝ := y*y
  have hx236 : Bounds (22024249 / 400000000) (13490929 / 244140625) x236 := by
    apply bounds_mul hy hy <;> norm_num
  let x237 : ℝ := -x236
  have hx237 : Bounds (-13490929 / 244140625) (-22024249 / 400000000) x237 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx236
  let x238 : ℝ := (1 / 1)+x237
  have hx238 : Bounds (230649696 / 244140625) (377975751 / 400000000) x238 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx237 <;> norm_num
  let x239 : ℝ := (1 / 1)-x236
  have hx239 : Bounds (230649696 / 244140625) (377975751 / 400000000) x239 := by
    exact hx238
  let x240 : ℝ := x239*x159
  have hx240 : Bounds (225892126923 / 1000000000000) (45272313561 / 200000000000) x240 := by
    apply bounds_mul hx239 hx159 <;> norm_num
  let x241 : ℝ := c*c
  have hx241 : Bounds (28389891049 / 1000000000000) (7123866409 / 250000000000) x241 := by
    apply bounds_mul hc hc <;> norm_num
  let x242 : ℝ := -x241
  have hx242 : Bounds (-7123866409 / 250000000000) (-28389891049 / 1000000000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx241
  let x243 : ℝ := (1 / 1)+x242
  have hx243 : Bounds (242876133591 / 250000000000) (971610108951 / 1000000000000) x243 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx242 <;> norm_num
  let x244 : ℝ := (1 / 1)-x241
  have hx244 : Bounds (242876133591 / 250000000000) (971610108951 / 1000000000000) x244 := by
    exact hx243
  let x245 : ℝ := x244*x182
  have hx245 : Bounds (274954249 / 400000000) (343756556501 / 500000000000) x245 := by
    apply bounds_mul hx244 hx182 <;> norm_num
  let x246 : ℝ := y*y
  have hx246 : Bounds (22024249 / 400000000) (13490929 / 244140625) x246 := by
    apply bounds_mul hy hy <;> norm_num
  let x247 : ℝ := (1 / 1)+x246
  have hx247 : Bounds (422024249 / 400000000) (257631554 / 244140625) x247 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx246 <;> norm_num
  let x248 : ℝ := x247*x159
  have hx248 : Bounds (63067509771 / 250000000000) (252788752721 / 1000000000000) x248 := by
    apply bounds_mul hx247 hx159 <;> norm_num
  let x249 : ℝ := -y
  have hx249 : Bounds (-3673 / 15625) (-4693 / 20000) x249 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x250 : ℝ := x248+x249
  have hx250 : Bounds (4299509771 / 250000000000) (18138752721 / 1000000000000) x250 := by
    apply bounds_add hx248 hx249 <;> norm_num
  let x251 : ℝ := x248-y
  have hx251 : Bounds (4299509771 / 250000000000) (18138752721 / 1000000000000) x251 := by
    exact hx250
  let x252 : ℝ := x240*x240
  have hx252 : Bounds (10205450601 / 200000000000) (2561977969 / 50000000000) x252 := by
    apply bounds_mul hx240 hx240 <;> norm_num
  let x253 : ℝ := x252⁻¹
  have hx253 : Bounds (2439521368109 / 125000000000) (783894833533 / 40000000000) x253 := by
    apply bounds_inv hx252 <;> norm_num
  let x254 : ℝ := x251*x253
  have hx254 : Bounds (335639870679 / 1000000000000) (355471863619 / 1000000000000) x254 := by
    apply bounds_mul hx251 hx253 <;> norm_num
  let x255 : ℝ := x251/x252
  have hx255 : Bounds (335639870679 / 1000000000000) (355471863619 / 1000000000000) x255 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx254
  let x256 : ℝ := (-2 / 1)*x255
  have hx256 : Bounds (-355471863619 / 500000000000) (-335639870679 / 500000000000) x256 := by
    apply bounds_mul (bounds_const ((-2 / 1) : ℝ)) hx255 <;> norm_num
  let x257 : ℝ := x256*x228
  have hx257 : Bounds (-63888687043 / 62500000000) (-192309166259 / 200000000000) x257 := by
    apply bounds_mul hx256 hx228 <;> norm_num
  let x258 : ℝ := (2 / 1)*x182
  have hx258 : Bounds (1415095037 / 1000000000) (283040741 / 200000000) x258 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx182 <;> norm_num
  let x259 : ℝ := c*c
  have hx259 : Bounds (28389891049 / 1000000000000) (7123866409 / 250000000000) x259 := by
    apply bounds_mul hc hc <;> norm_num
  let x260 : ℝ := -x259
  have hx260 : Bounds (-7123866409 / 250000000000) (-28389891049 / 1000000000000) x260 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx259
  let x261 : ℝ := x258+x260
  have hx261 : Bounds (346649892841 / 250000000000) (1386813813951 / 1000000000000) x261 := by
    apply bounds_add hx258 hx260 <;> norm_num
  let x262 : ℝ := x258-x259
  have hx262 : Bounds (346649892841 / 250000000000) (1386813813951 / 1000000000000) x262 := by
    exact hx261
  let x263 : ℝ := c*x262
  have hx263 : Bounds (233632321577 / 1000000000000) (117051246339 / 500000000000) x263 := by
    apply bounds_mul hc hx262 <;> norm_num
  let x264 : ℝ := x245*x245
  have hx264 : Bounds (472498994019 / 1000000000000) (9453485611 / 20000000000) x264 := by
    apply bounds_mul hx245 hx245 <;> norm_num
  let x265 : ℝ := x264⁻¹
  have hx265 : Bounds (528905443531 / 250000000000) (52910165559 / 25000000000) x265 := by
    apply bounds_inv hx264 <;> norm_num
  let x266 : ℝ := x263*x265
  have hx266 : Bounds (494277626667 / 1000000000000) (99091213163 / 200000000000) x266 := by
    apply bounds_mul hx263 hx265 <;> norm_num
  let x267 : ℝ := x263/x264
  have hx267 : Bounds (494277626667 / 1000000000000) (99091213163 / 200000000000) x267 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx266
  let x268 : ℝ := (2 / 1)*x267
  have hx268 : Bounds (494277626667 / 500000000000) (99091213163 / 100000000000) x268 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx267 <;> norm_num
  let x269 : ℝ := x268*x235
  have hx269 : Bounds (262494506073 / 250000000000) (1053179011149 / 1000000000000) x269 := by
    apply bounds_mul hx268 hx235 <;> norm_num
  let x270 : ℝ := x257+x269
  have hx270 : Bounds (6939757901 / 250000000000) (45816589927 / 500000000000) x270 := by
    apply bounds_add hx257 hx269 <;> norm_num
  have hPos : 0 < x270 :=
    lt_of_lt_of_le (by norm_num) hx270.1
  have hBridgeL : doubleCapBridgeL x = x48 := by
    exact hEll'
  rw [← doubleCapBridgeDerivativeTraceForm_eq x]
  simpa +zetaDelta only [doubleCapBridgeDerivativeTraceForm,
    hBridgeL, SmallMean.A, biasB, div_one, pow_two] using hPos

theorem acceptedCell : DoubleCapBridgeDerivativeCellCertificate
    (⟨137, by decide⟩ : Fin 256) doubleCapBridgeDerivativeExpression where
  positive x hx := by
    have hloEq : doubleCapBridgeLo (⟨137, by decide⟩ : Fin 256) =
        (1691 / 10240) := by norm_num [doubleCapBridgeLo, doubleCapBridgeStep]
    have hhiEq : doubleCapBridgeHi (⟨137, by decide⟩ : Fin 256) =
        (847 / 5120) := by norm_num [doubleCapBridgeHi, doubleCapBridgeStep]
    have hlo : (1691 / 10240) ≤ x := by
      simpa only [hloEq] using hx.1
    have hhi : x ≤ (847 / 5120) := by
      simpa only [hhiEq] using hx.2
    exact cell_derivative_pos x ⟨hlo, hhi⟩

#print axioms cell_derivative_pos
#print axioms acceptedCell

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell137

end


