-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell018__4
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell018__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T14:33:51.694902+00:00
-- url     : https://prove2.me/theorems/110f0167-e3dd-4b01-91a1-88ec608ed31a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell018 (+3 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell019, Ge…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell018 (+3 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell019, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell020, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell021)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell018 (+3 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell019, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell020, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell021)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell018 (+3 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell019, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell020, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell021) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell018 (+3 modules: GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell019, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell020, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell021).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapHighMiddleDerivativeTraceForm
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell017Logs__6

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell018 =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell018
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_derivative_pos (x : ℝ)
    (hx : Bounds (667 / 5120) (1337 / 10240) x) :
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
  have hx0 : Bounds (667 / 2560) (1337 / 5120) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx <;> norm_num
  let x1 : ℝ := Real.log (2 / 1)
  have hx1 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x1 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x2 : ℝ := Real.log (2 / 1)
  have hx2 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x2 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x3 : ℝ := (1 / 1)+(1337 / 5120)
  have hx3 : Bounds (6457 / 5120) (6457 / 5120) x3 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1337 / 5120) : ℝ)) <;> norm_num
  let x4 : ℝ := (1 / 1)+(1337 / 5120)
  have hx4 : Bounds (6457 / 5120) (6457 / 5120) x4 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1337 / 5120) : ℝ)) <;> norm_num
  let x5 : ℝ := Real.log x4
  have hx5 : Bounds (116005187 / 500000000) (1856083 / 8000000) x5 := by
    exact bounds_log hx4 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x6 : ℝ := x3*x5
  have hx6 : Bounds (292595895491 / 1000000000000) (292595896753 / 1000000000000) x6 := by
    apply bounds_mul hx3 hx5 <;> norm_num
  let x7 : ℝ := -(1337 / 5120)
  have hx7 : Bounds (-1337 / 5120) (-1337 / 5120) x7 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1337 / 5120) : ℝ))
  let x8 : ℝ := (1 / 1)+x7
  have hx8 : Bounds (3783 / 5120) (3783 / 5120) x8 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx7 <;> norm_num
  let x9 : ℝ := (1 / 1)-(1337 / 5120)
  have hx9 : Bounds (3783 / 5120) (3783 / 5120) x9 := by
    exact hx8
  let x10 : ℝ := -(1337 / 5120)
  have hx10 : Bounds (-1337 / 5120) (-1337 / 5120) x10 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1337 / 5120) : ℝ))
  let x11 : ℝ := (1 / 1)+x10
  have hx11 : Bounds (3783 / 5120) (3783 / 5120) x11 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx10 <;> norm_num
  let x12 : ℝ := (1 / 1)-(1337 / 5120)
  have hx12 : Bounds (3783 / 5120) (3783 / 5120) x12 := by
    exact hx11
  let x13 : ℝ := Real.log x12
  have hx13 : Bounds (-151318547 / 500000000) (-302637093 / 1000000000) x13 := by
    exact bounds_log hx12 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x14 : ℝ := x9*x13
  have hx14 : Bounds (-223608618477 / 1000000000000) (-111804308869 / 500000000000) x14 := by
    apply bounds_mul hx9 hx13 <;> norm_num
  let x15 : ℝ := x6+x14
  have hx15 : Bounds (34493638507 / 500000000000) (13797455803 / 200000000000) x15 := by
    apply bounds_add hx6 hx14 <;> norm_num
  let x16 : ℝ := (2 / 1)⁻¹
  have hx16 : Bounds (1 / 2) (1 / 2) x16 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x17 : ℝ := x15*x16
  have hx17 : Bounds (34493638507 / 1000000000000) (8623409877 / 250000000000) x17 := by
    apply bounds_mul hx15 hx16 <;> norm_num
  let x18 : ℝ := x15/(2 / 1)
  have hx18 : Bounds (34493638507 / 1000000000000) (8623409877 / 250000000000) x18 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx17
  let x19 : ℝ := -x18
  have hx19 : Bounds (-8623409877 / 250000000000) (-34493638507 / 1000000000000) x19 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx18
  let x20 : ℝ := x2+x19
  have hx20 : Bounds (164663385123 / 250000000000) (658653542493 / 1000000000000) x20 := by
    apply bounds_add hx2 hx19 <;> norm_num
  let x21 : ℝ := x2-x18
  have hx21 : Bounds (164663385123 / 250000000000) (658653542493 / 1000000000000) x21 := by
    exact hx20
  let x22 : ℝ := biasE (1337 / 5120)
  have hx22 : Bounds (164663385123 / 250000000000) (658653542493 / 1000000000000) x22 := by
    simpa +zetaDelta only [biasE, div_one] using hx21
  let x23 : ℝ := Real.log (2 / 1)
  have hx23 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x23 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x24 : ℝ := (1 / 1)+(667 / 2560)
  have hx24 : Bounds (3227 / 2560) (3227 / 2560) x24 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((667 / 2560) : ℝ)) <;> norm_num
  let x25 : ℝ := (1 / 1)+(667 / 2560)
  have hx25 : Bounds (3227 / 2560) (3227 / 2560) x25 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((667 / 2560) : ℝ)) <;> norm_num
  let x26 : ℝ := Real.log x25
  have hx26 : Bounds (115772827 / 500000000) (46309131 / 200000000) x26 := by
    exact bounds_log hx25 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x27 : ℝ := x24*x26
  have hx27 : Bounds (291874150569 / 1000000000000) (291874151831 / 1000000000000) x27 := by
    apply bounds_mul hx24 hx26 <;> norm_num
  let x28 : ℝ := -(667 / 2560)
  have hx28 : Bounds (-667 / 2560) (-667 / 2560) x28 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((667 / 2560) : ℝ))
  let x29 : ℝ := (1 / 1)+x28
  have hx29 : Bounds (1893 / 2560) (1893 / 2560) x29 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx28 <;> norm_num
  let x30 : ℝ := (1 / 1)-(667 / 2560)
  have hx30 : Bounds (1893 / 2560) (1893 / 2560) x30 := by
    exact hx29
  let x31 : ℝ := -(667 / 2560)
  have hx31 : Bounds (-667 / 2560) (-667 / 2560) x31 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((667 / 2560) : ℝ))
  let x32 : ℝ := (1 / 1)+x31
  have hx32 : Bounds (1893 / 2560) (1893 / 2560) x32 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx31 <;> norm_num
  let x33 : ℝ := (1 / 1)-(667 / 2560)
  have hx33 : Bounds (1893 / 2560) (1893 / 2560) x33 := by
    exact hx32
  let x34 : ℝ := Real.log x33
  have hx34 : Bounds (-301844387 / 1000000000) (-150922193 / 500000000) x34 := by
    exact bounds_log hx33 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x35 : ℝ := x30*x34
  have hx35 : Bounds (-223199775231 / 1000000000000) (-223199774491 / 1000000000000) x35 := by
    apply bounds_mul hx30 hx34 <;> norm_num
  let x36 : ℝ := x27+x35
  have hx36 : Bounds (34337187669 / 500000000000) (3433718867 / 50000000000) x36 := by
    apply bounds_add hx27 hx35 <;> norm_num
  let x37 : ℝ := (2 / 1)⁻¹
  have hx37 : Bounds (1 / 2) (1 / 2) x37 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x38 : ℝ := x36*x37
  have hx38 : Bounds (34337187669 / 1000000000000) (3433718867 / 100000000000) x38 := by
    apply bounds_mul hx36 hx37 <;> norm_num
  let x39 : ℝ := x36/(2 / 1)
  have hx39 : Bounds (34337187669 / 1000000000000) (3433718867 / 100000000000) x39 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx38
  let x40 : ℝ := -x39
  have hx40 : Bounds (-3433718867 / 100000000000) (-34337187669 / 1000000000000) x40 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx39
  let x41 : ℝ := x23+x40
  have hx41 : Bounds (65880999133 / 100000000000) (658809993331 / 1000000000000) x41 := by
    apply bounds_add hx23 hx40 <;> norm_num
  let x42 : ℝ := x23-x39
  have hx42 : Bounds (65880999133 / 100000000000) (658809993331 / 1000000000000) x42 := by
    exact hx41
  let x43 : ℝ := biasE (667 / 2560)
  have hx43 : Bounds (65880999133 / 100000000000) (658809993331 / 1000000000000) x43 := by
    simpa +zetaDelta only [biasE, div_one] using hx42
  let x44 : ℝ := biasE x0
  have hx44 : Bounds (164663385123 / 250000000000) (658809993331 / 1000000000000) x44 := by
    exact bounds_biasE hx0 (by norm_num) (by norm_num) hx22.1 hx43.2
  let x45 : ℝ := x1+x44
  have hx45 : Bounds (337950180123 / 250000000000) (1351957174331 / 1000000000000) x45 := by
    apply bounds_add hx1 hx44 <;> norm_num
  let x46 : ℝ := (2 / 1)⁻¹
  have hx46 : Bounds (1 / 2) (1 / 2) x46 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x47 : ℝ := x45*x46
  have hx47 : Bounds (337950180123 / 500000000000) (337989293583 / 500000000000) x47 := by
    apply bounds_mul hx45 hx46 <;> norm_num
  let x48 : ℝ := x45/(2 / 1)
  have hx48 : Bounds (337950180123 / 500000000000) (337989293583 / 500000000000) x48 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx47
  let x49 : ℝ := Real.log (2 / 1)
  have hx49 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x49 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x50 : ℝ := (1 / 1)+(18477 / 100000)
  have hx50 : Bounds (118477 / 100000) (118477 / 100000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((18477 / 100000) : ℝ)) <;> norm_num
  let x51 : ℝ := (1 / 1)+(18477 / 100000)
  have hx51 : Bounds (118477 / 100000) (118477 / 100000) x51 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((18477 / 100000) : ℝ)) <;> norm_num
  let x52 : ℝ := Real.log x51
  have hx52 : Bounds (84774331 / 500000000) (169548663 / 1000000000) x52 := by
    exact bounds_log hx51 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x53 : ℝ := x50*x52
  have hx53 : Bounds (200876168277 / 1000000000000) (200876169463 / 1000000000000) x53 := by
    apply bounds_mul hx50 hx52 <;> norm_num
  let x54 : ℝ := -(18477 / 100000)
  have hx54 : Bounds (-18477 / 100000) (-18477 / 100000) x54 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((18477 / 100000) : ℝ))
  let x55 : ℝ := (1 / 1)+x54
  have hx55 : Bounds (81523 / 100000) (81523 / 100000) x55 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx54 <;> norm_num
  let x56 : ℝ := (1 / 1)-(18477 / 100000)
  have hx56 : Bounds (81523 / 100000) (81523 / 100000) x56 := by
    exact hx55
  let x57 : ℝ := -(18477 / 100000)
  have hx57 : Bounds (-18477 / 100000) (-18477 / 100000) x57 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((18477 / 100000) : ℝ))
  let x58 : ℝ := (1 / 1)+x57
  have hx58 : Bounds (81523 / 100000) (81523 / 100000) x58 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx57 <;> norm_num
  let x59 : ℝ := (1 / 1)-(18477 / 100000)
  have hx59 : Bounds (81523 / 100000) (81523 / 100000) x59 := by
    exact hx58
  let x60 : ℝ := Real.log x59
  have hx60 : Bounds (-204284997 / 1000000000) (-51071249 / 250000000) x60 := by
    exact bounds_log hx59 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x61 : ℝ := x56*x60
  have hx61 : Bounds (-33307851621 / 200000000000) (-166539257289 / 1000000000000) x61 := by
    apply bounds_mul hx56 hx60 <;> norm_num
  let x62 : ℝ := x53+x61
  have hx62 : Bounds (8584227543 / 250000000000) (17168456087 / 500000000000) x62 := by
    apply bounds_add hx53 hx61 <;> norm_num
  let x63 : ℝ := (2 / 1)⁻¹
  have hx63 : Bounds (1 / 2) (1 / 2) x63 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x64 : ℝ := x62*x63
  have hx64 : Bounds (8584227543 / 500000000000) (17168456087 / 1000000000000) x64 := by
    apply bounds_mul hx62 hx63 <;> norm_num
  let x65 : ℝ := x62/(2 / 1)
  have hx65 : Bounds (8584227543 / 500000000000) (17168456087 / 1000000000000) x65 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx64
  let x66 : ℝ := -x65
  have hx66 : Bounds (-17168456087 / 1000000000000) (-8584227543 / 500000000000) x66 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx65
  let x67 : ℝ := x49+x66
  have hx67 : Bounds (675978723913 / 1000000000000) (337989362957 / 500000000000) x67 := by
    apply bounds_add hx49 hx66 <;> norm_num
  let x68 : ℝ := x49-x65
  have hx68 : Bounds (675978723913 / 1000000000000) (337989362957 / 500000000000) x68 := by
    exact hx67
  let x69 : ℝ := biasE (18477 / 100000)
  have hx69 : Bounds (675978723913 / 1000000000000) (337989362957 / 500000000000) x69 := by
    simpa +zetaDelta only [biasE, div_one] using hx68
  let x70 : ℝ := Real.log (2 / 1)
  have hx70 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x70 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x71 : ℝ := (1 / 1)+(185189 / 1000000)
  have hx71 : Bounds (1185189 / 1000000) (1185189 / 1000000) x71 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((185189 / 1000000) : ℝ)) <;> norm_num
  let x72 : ℝ := (1 / 1)+(185189 / 1000000)
  have hx72 : Bounds (1185189 / 1000000) (1185189 / 1000000) x72 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((185189 / 1000000) : ℝ)) <;> norm_num
  let x73 : ℝ := Real.log x72
  have hx73 : Bounds (33980451 / 200000000) (10618891 / 62500000) x73 := by
    exact bounds_log hx72 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x74 : ℝ := x71*x73
  have hx74 : Bounds (201366283701 / 1000000000000) (201366284887 / 1000000000000) x74 := by
    apply bounds_mul hx71 hx73 <;> norm_num
  let x75 : ℝ := -(185189 / 1000000)
  have hx75 : Bounds (-185189 / 1000000) (-185189 / 1000000) x75 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((185189 / 1000000) : ℝ))
  let x76 : ℝ := (1 / 1)+x75
  have hx76 : Bounds (814811 / 1000000) (814811 / 1000000) x76 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx75 <;> norm_num
  let x77 : ℝ := (1 / 1)-(185189 / 1000000)
  have hx77 : Bounds (814811 / 1000000) (814811 / 1000000) x77 := by
    exact hx76
  let x78 : ℝ := -(185189 / 1000000)
  have hx78 : Bounds (-185189 / 1000000) (-185189 / 1000000) x78 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((185189 / 1000000) : ℝ))
  let x79 : ℝ := (1 / 1)+x78
  have hx79 : Bounds (814811 / 1000000) (814811 / 1000000) x79 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx78 <;> norm_num
  let x80 : ℝ := (1 / 1)-(185189 / 1000000)
  have hx80 : Bounds (814811 / 1000000) (814811 / 1000000) x80 := by
    exact hx79
  let x81 : ℝ := Real.log x80
  have hx81 : Bounds (-40959819 / 200000000) (-102399547 / 500000000) x81 := by
    exact bounds_log hx80 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x82 : ℝ := x77*x81
  have hx82 : Bounds (-166872555397 / 1000000000000) (-166872554581 / 1000000000000) x82 := by
    apply bounds_mul hx77 hx81 <;> norm_num
  let x83 : ℝ := x74+x82
  have hx83 : Bounds (2155858019 / 62500000000) (17246865153 / 500000000000) x83 := by
    apply bounds_add hx74 hx82 <;> norm_num
  let x84 : ℝ := (2 / 1)⁻¹
  have hx84 : Bounds (1 / 2) (1 / 2) x84 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x85 : ℝ := x83*x84
  have hx85 : Bounds (2155858019 / 125000000000) (17246865153 / 1000000000000) x85 := by
    apply bounds_mul hx83 hx84 <;> norm_num
  let x86 : ℝ := x83/(2 / 1)
  have hx86 : Bounds (2155858019 / 125000000000) (17246865153 / 1000000000000) x86 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx85
  let x87 : ℝ := -x86
  have hx87 : Bounds (-17246865153 / 1000000000000) (-2155858019 / 125000000000) x87 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx86
  let x88 : ℝ := x70+x87
  have hx88 : Bounds (675900314847 / 1000000000000) (42243769803 / 62500000000) x88 := by
    apply bounds_add hx70 hx87 <;> norm_num
  let x89 : ℝ := x70-x86
  have hx89 : Bounds (675900314847 / 1000000000000) (42243769803 / 62500000000) x89 := by
    exact hx88
  let x90 : ℝ := biasE (185189 / 1000000)
  have hx90 : Bounds (675900314847 / 1000000000000) (42243769803 / 62500000000) x90 := by
    simpa +zetaDelta only [biasE, div_one] using hx89
  let y : ℝ := doubleCapHighTailY x
  have hEll' : Real.log 2 * doubleCapHighTailFloor x = x48 := by
    simpa +zetaDelta only [div_one] using hEll
  have hy : Bounds (18477 / 100000) (185189 / 1000000) y := by
    dsimp only [y, doubleCapHighTailY]
    apply entropyInverseBias_bracket hh0.le hh1.le
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (185189 / 1000000) ≤ (42243769803 / 62500000000) := hx90.2
      have h2 : (337950180123 / 500000000000) ≤ x48 := hx48.1
      linarith [hEll']
    · have h1 : x48 ≤ (337989293583 / 500000000000) := hx48.2
      have h2 : (675978723913 / 1000000000000) ≤ biasE (18477 / 100000) := hx69.1
      linarith [hEll']
  let x91 : ℝ := x⁻¹
  have hx91 : Bounds (3829468960359 / 500000000000) (7676161919041 / 1000000000000) x91 := by
    apply bounds_inv hx <;> norm_num
  let x92 : ℝ := x48*x91
  have hx92 : Bounds (1035335779943 / 200000000000) (5188921088891 / 1000000000000) x92 := by
    apply bounds_mul hx48 hx91 <;> norm_num
  let x93 : ℝ := x48/x
  have hx93 : Bounds (1035335779943 / 200000000000) (5188921088891 / 1000000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(1319 / 10000)
  have hx95 : Bounds (11319 / 10000) (11319 / 10000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1319 / 10000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(1319 / 10000)
  have hx96 : Bounds (11319 / 10000) (11319 / 10000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1319 / 10000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (30974409 / 250000000) (123897637 / 1000000000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (35059933547 / 250000000000) (140239735321 / 1000000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(1319 / 10000)
  have hx99 : Bounds (-1319 / 10000) (-1319 / 10000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1319 / 10000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (8681 / 10000) (8681 / 10000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(1319 / 10000)
  have hx101 : Bounds (8681 / 10000) (8681 / 10000) x101 := by
    exact hx100
  let x102 : ℝ := -(1319 / 10000)
  have hx102 : Bounds (-1319 / 10000) (-1319 / 10000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1319 / 10000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (8681 / 10000) (8681 / 10000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(1319 / 10000)
  have hx104 : Bounds (8681 / 10000) (8681 / 10000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-35362091 / 250000000) (-141448363 / 1000000000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-122791324789 / 1000000000000) (-1534891549 / 12500000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (17448409399 / 1000000000000) (17448411401 / 1000000000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (8724204699 / 1000000000000) (8724205701 / 1000000000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (8724204699 / 1000000000000) (8724205701 / 1000000000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-8724205701 / 1000000000000) (-8724204699 / 1000000000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (684422974299 / 1000000000000) (684422976301 / 1000000000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (684422974299 / 1000000000000) (684422976301 / 1000000000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (1319 / 10000)
  have hx114 : Bounds (684422974299 / 1000000000000) (684422976301 / 1000000000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(26441 / 200000)
  have hx116 : Bounds (226441 / 200000) (226441 / 200000) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((26441 / 200000) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(26441 / 200000)
  have hx117 : Bounds (226441 / 200000) (226441 / 200000) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((26441 / 200000) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (62083529 / 500000000) (124167059 / 1000000000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (70291281951 / 500000000000) (35145641259 / 250000000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(26441 / 200000)
  have hx120 : Bounds (-26441 / 200000) (-26441 / 200000) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((26441 / 200000) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (173559 / 200000) (173559 / 200000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(26441 / 200000)
  have hx122 : Bounds (173559 / 200000) (173559 / 200000) x122 := by
    exact hx121
  let x123 : ℝ := -(26441 / 200000)
  have hx123 : Bounds (-26441 / 200000) (-26441 / 200000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((26441 / 200000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (173559 / 200000) (173559 / 200000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(26441 / 200000)
  have hx125 : Bounds (173559 / 200000) (173559 / 200000) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-17724971 / 125000000) (-141799767 / 1000000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-15381641209 / 125000000000) (-123053128803 / 1000000000000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (1752943423 / 100000000000) (17529436233 / 1000000000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (1752943423 / 200000000000) (8764718117 / 1000000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (1752943423 / 200000000000) (8764718117 / 1000000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-8764718117 / 1000000000000) (-1752943423 / 200000000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (684382461883 / 1000000000000) (136876492777 / 200000000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (684382461883 / 1000000000000) (136876492777 / 200000000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (26441 / 200000)
  have hx135 : Bounds (684382461883 / 1000000000000) (136876492777 / 200000000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(1319 / 10000)
  have hx136 : Bounds (85350493359 / 125000000000) (5475349533 / 8000000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((1319 / 10000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(26441 / 200000)
  have hx137 : Bounds (42773927121 / 62500000000) (686001312557 / 1000000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((26441 / 200000) : ℝ)) <;> norm_num
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
  have hc : Bounds (1319 / 10000) (26441 / 200000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num)
      (by norm_num) (show 0 < x93 by linarith [hx93.1]) hcEq
    · have h1 : x93 * (1319 / 10000) ≤ (5475349533 / 8000000000) := hx136.2
      have h2 : (684422974299 / 1000000000000) ≤ biasE (1319 / 10000) := hx114.1
      linarith
    · have h1 : biasE (26441 / 200000) ≤ (136876492777 / 200000000000) := hx135.2
      have h2 : (42773927121 / 62500000000) ≤ x93 * (26441 / 200000) := hx137.1
      linarith
  let x138 : ℝ := (1 / 1)+x0
  have hx138 : Bounds (3227 / 2560) (6457 / 5120) x138 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx0 <;> norm_num
  let x139 : ℝ := -x0
  have hx139 : Bounds (-1337 / 5120) (-667 / 2560) x139 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x140 : ℝ := (1 / 1)+x139
  have hx140 : Bounds (3783 / 5120) (1893 / 2560) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx139 <;> norm_num
  let x141 : ℝ := (1 / 1)-x0
  have hx141 : Bounds (3783 / 5120) (1893 / 2560) x141 := by
    exact hx140
  let x142 : ℝ := x141⁻¹
  have hx142 : Bounds (1352350765979 / 1000000000000) (676711604547 / 500000000000) x142 := by
    apply bounds_inv hx141 <;> norm_num
  let x143 : ℝ := x138*x142
  have hx143 : Bounds (852350765979 / 500000000000) (426711604547 / 250000000000) x143 := by
    apply bounds_mul hx138 hx142 <;> norm_num
  let x144 : ℝ := x138/x141
  have hx144 : Bounds (852350765979 / 500000000000) (426711604547 / 250000000000) x144 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx143
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (13334751 / 25000000) (133661867 / 250000000) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_14.2)
  let x146 : ℝ := (2 / 1)⁻¹
  have hx146 : Bounds (1 / 2) (1 / 2) x146 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x147 : ℝ := x145*x146
  have hx147 : Bounds (13334751 / 50000000) (133661867 / 500000000) x147 := by
    apply bounds_mul hx145 hx146 <;> norm_num
  let x148 : ℝ := x145/(2 / 1)
  have hx148 : Bounds (13334751 / 50000000) (133661867 / 500000000) x148 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx147
  let x149 : ℝ := (1 / 1)+y
  have hx149 : Bounds (118477 / 100000) (1185189 / 1000000) x149 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x150 : ℝ := -y
  have hx150 : Bounds (-185189 / 1000000) (-18477 / 100000) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (814811 / 1000000) (81523 / 100000) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-y
  have hx152 : Bounds (814811 / 1000000) (81523 / 100000) x152 := by
    exact hx151
  let x153 : ℝ := x152⁻¹
  have hx153 : Bounds (245329538903 / 200000000000) (76704904573 / 62500000000) x153 := by
    apply bounds_inv hx152 <;> norm_num
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (145329538903 / 100000000000) (45454904573 / 31250000000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x149/x152
  have hx155 : Bounds (145329538903 / 100000000000) (45454904573 / 31250000000) x155 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx154
  let x156 : ℝ := Real.log x155
  have hx156 : Bounds (373833659 / 1000000000) (374701351 / 1000000000) x156 := by
    exact bounds_log hx155 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_16.2)
  let x157 : ℝ := (2 / 1)⁻¹
  have hx157 : Bounds (1 / 2) (1 / 2) x157 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x158 : ℝ := x156*x157
  have hx158 : Bounds (373833659 / 2000000000) (374701351 / 2000000000) x158 := by
    apply bounds_mul hx156 hx157 <;> norm_num
  let x159 : ℝ := x156/(2 / 1)
  have hx159 : Bounds (373833659 / 2000000000) (374701351 / 2000000000) x159 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx158
  let x160 : ℝ := (1 / 1)+c
  have hx160 : Bounds (11319 / 10000) (226441 / 200000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x161 : ℝ := -c
  have hx161 : Bounds (-26441 / 200000) (-1319 / 10000) x161 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x162 : ℝ := (1 / 1)+x161
  have hx162 : Bounds (173559 / 200000) (8681 / 10000) x162 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx161 <;> norm_num
  let x163 : ℝ := (1 / 1)-c
  have hx163 : Bounds (173559 / 200000) (8681 / 10000) x163 := by
    exact hx162
  let x164 : ℝ := x163⁻¹
  have hx164 : Bounds (1151941020619 / 1000000000000) (576172944071 / 500000000000) x164 := by
    apply bounds_inv hx163 <;> norm_num
  let x165 : ℝ := x160*x164
  have hx165 : Bounds (651941020619 / 500000000000) (326172944071 / 250000000000) x165 := by
    apply bounds_mul hx160 hx164 <;> norm_num
  let x166 : ℝ := x160/x163
  have hx166 : Bounds (651941020619 / 500000000000) (326172944071 / 250000000000) x166 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx165
  let x167 : ℝ := Real.log x166
  have hx167 : Bounds (132673 / 500000) (265966827 / 1000000000) x167 := by
    exact bounds_log hx166 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x168 : ℝ := (2 / 1)⁻¹
  have hx168 : Bounds (1 / 2) (1 / 2) x168 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x169 : ℝ := x167*x168
  have hx169 : Bounds (132673 / 1000000) (265966827 / 2000000000) x169 := by
    apply bounds_mul hx167 hx168 <;> norm_num
  let x170 : ℝ := x167/(2 / 1)
  have hx170 : Bounds (132673 / 1000000) (265966827 / 2000000000) x170 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx169
  let x171 : ℝ := Real.log (2 / 1)
  have hx171 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x171 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x172 : ℝ := c*c
  have hx172 : Bounds (1739761 / 100000000) (699126481 / 40000000000) x172 := by
    apply bounds_mul hc hc <;> norm_num
  let x173 : ℝ := -x172
  have hx173 : Bounds (-699126481 / 40000000000) (-1739761 / 100000000) x173 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx172
  let x174 : ℝ := (1 / 1)+x173
  have hx174 : Bounds (39300873519 / 40000000000) (98260239 / 100000000) x174 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx173 <;> norm_num
  let x175 : ℝ := (1 / 1)-x172
  have hx175 : Bounds (39300873519 / 40000000000) (98260239 / 100000000) x175 := by
    exact hx174
  let x176 : ℝ := Real.log x175
  have hx176 : Bounds (-17632709 / 1000000000) (-8775363 / 500000000) x176 := by
    exact bounds_log hx175 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (-17632709 / 2000000000) (-8775363 / 1000000000) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (-17632709 / 2000000000) (-8775363 / 1000000000) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (8775363 / 1000000000) (17632709 / 2000000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x171+x180
  have hx181 : Bounds (701922543 / 1000000000) (1403927071 / 2000000000) x181 := by
    apply bounds_add hx171 hx180 <;> norm_num
  let x182 : ℝ := x171-x179
  have hx182 : Bounds (701922543 / 1000000000) (1403927071 / 2000000000) x182 := by
    exact hx181
  let x183 : ℝ := Real.log (2 / 1)
  have hx183 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x183 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x184 : ℝ := (1 / 1)+(26441 / 200000)
  have hx184 : Bounds (226441 / 200000) (226441 / 200000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((26441 / 200000) : ℝ)) <;> norm_num
  let x185 : ℝ := (1 / 1)+(26441 / 200000)
  have hx185 : Bounds (226441 / 200000) (226441 / 200000) x185 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((26441 / 200000) : ℝ)) <;> norm_num
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (62083529 / 500000000) (124167059 / 1000000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x187 : ℝ := x184*x186
  have hx187 : Bounds (70291281951 / 500000000000) (35145641259 / 250000000000) x187 := by
    apply bounds_mul hx184 hx186 <;> norm_num
  let x188 : ℝ := -(26441 / 200000)
  have hx188 : Bounds (-26441 / 200000) (-26441 / 200000) x188 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((26441 / 200000) : ℝ))
  let x189 : ℝ := (1 / 1)+x188
  have hx189 : Bounds (173559 / 200000) (173559 / 200000) x189 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx188 <;> norm_num
  let x190 : ℝ := (1 / 1)-(26441 / 200000)
  have hx190 : Bounds (173559 / 200000) (173559 / 200000) x190 := by
    exact hx189
  let x191 : ℝ := -(26441 / 200000)
  have hx191 : Bounds (-26441 / 200000) (-26441 / 200000) x191 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((26441 / 200000) : ℝ))
  let x192 : ℝ := (1 / 1)+x191
  have hx192 : Bounds (173559 / 200000) (173559 / 200000) x192 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx191 <;> norm_num
  let x193 : ℝ := (1 / 1)-(26441 / 200000)
  have hx193 : Bounds (173559 / 200000) (173559 / 200000) x193 := by
    exact hx192
  let x194 : ℝ := Real.log x193
  have hx194 : Bounds (-17724971 / 125000000) (-141799767 / 1000000000) x194 := by
    exact bounds_log hx193 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x195 : ℝ := x190*x194
  have hx195 : Bounds (-15381641209 / 125000000000) (-123053128803 / 1000000000000) x195 := by
    apply bounds_mul hx190 hx194 <;> norm_num
  let x196 : ℝ := x187+x195
  have hx196 : Bounds (1752943423 / 100000000000) (17529436233 / 1000000000000) x196 := by
    apply bounds_add hx187 hx195 <;> norm_num
  let x197 : ℝ := (2 / 1)⁻¹
  have hx197 : Bounds (1 / 2) (1 / 2) x197 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x198 : ℝ := x196*x197
  have hx198 : Bounds (1752943423 / 200000000000) (8764718117 / 1000000000000) x198 := by
    apply bounds_mul hx196 hx197 <;> norm_num
  let x199 : ℝ := x196/(2 / 1)
  have hx199 : Bounds (1752943423 / 200000000000) (8764718117 / 1000000000000) x199 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx198
  let x200 : ℝ := -x199
  have hx200 : Bounds (-8764718117 / 1000000000000) (-1752943423 / 200000000000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx199
  let x201 : ℝ := x183+x200
  have hx201 : Bounds (684382461883 / 1000000000000) (136876492777 / 200000000000) x201 := by
    apply bounds_add hx183 hx200 <;> norm_num
  let x202 : ℝ := x183-x199
  have hx202 : Bounds (684382461883 / 1000000000000) (136876492777 / 200000000000) x202 := by
    exact hx201
  let x203 : ℝ := biasE (26441 / 200000)
  have hx203 : Bounds (684382461883 / 1000000000000) (136876492777 / 200000000000) x203 := by
    simpa +zetaDelta only [biasE, div_one] using hx202
  let x204 : ℝ := Real.log (2 / 1)
  have hx204 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x204 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x205 : ℝ := (1 / 1)+(1319 / 10000)
  have hx205 : Bounds (11319 / 10000) (11319 / 10000) x205 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1319 / 10000) : ℝ)) <;> norm_num
  let x206 : ℝ := (1 / 1)+(1319 / 10000)
  have hx206 : Bounds (11319 / 10000) (11319 / 10000) x206 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1319 / 10000) : ℝ)) <;> norm_num
  let x207 : ℝ := Real.log x206
  have hx207 : Bounds (30974409 / 250000000) (123897637 / 1000000000) x207 := by
    exact bounds_log hx206 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x208 : ℝ := x205*x207
  have hx208 : Bounds (35059933547 / 250000000000) (140239735321 / 1000000000000) x208 := by
    apply bounds_mul hx205 hx207 <;> norm_num
  let x209 : ℝ := -(1319 / 10000)
  have hx209 : Bounds (-1319 / 10000) (-1319 / 10000) x209 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1319 / 10000) : ℝ))
  let x210 : ℝ := (1 / 1)+x209
  have hx210 : Bounds (8681 / 10000) (8681 / 10000) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx209 <;> norm_num
  let x211 : ℝ := (1 / 1)-(1319 / 10000)
  have hx211 : Bounds (8681 / 10000) (8681 / 10000) x211 := by
    exact hx210
  let x212 : ℝ := -(1319 / 10000)
  have hx212 : Bounds (-1319 / 10000) (-1319 / 10000) x212 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1319 / 10000) : ℝ))
  let x213 : ℝ := (1 / 1)+x212
  have hx213 : Bounds (8681 / 10000) (8681 / 10000) x213 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx212 <;> norm_num
  let x214 : ℝ := (1 / 1)-(1319 / 10000)
  have hx214 : Bounds (8681 / 10000) (8681 / 10000) x214 := by
    exact hx213
  let x215 : ℝ := Real.log x214
  have hx215 : Bounds (-35362091 / 250000000) (-141448363 / 1000000000) x215 := by
    exact bounds_log hx214 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x216 : ℝ := x211*x215
  have hx216 : Bounds (-122791324789 / 1000000000000) (-1534891549 / 12500000000) x216 := by
    apply bounds_mul hx211 hx215 <;> norm_num
  let x217 : ℝ := x208+x216
  have hx217 : Bounds (17448409399 / 1000000000000) (17448411401 / 1000000000000) x217 := by
    apply bounds_add hx208 hx216 <;> norm_num
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (8724204699 / 1000000000000) (8724205701 / 1000000000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (8724204699 / 1000000000000) (8724205701 / 1000000000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := -x220
  have hx221 : Bounds (-8724205701 / 1000000000000) (-8724204699 / 1000000000000) x221 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx220
  let x222 : ℝ := x204+x221
  have hx222 : Bounds (684422974299 / 1000000000000) (684422976301 / 1000000000000) x222 := by
    apply bounds_add hx204 hx221 <;> norm_num
  let x223 : ℝ := x204-x220
  have hx223 : Bounds (684422974299 / 1000000000000) (684422976301 / 1000000000000) x223 := by
    exact hx222
  let x224 : ℝ := biasE (1319 / 10000)
  have hx224 : Bounds (684422974299 / 1000000000000) (684422976301 / 1000000000000) x224 := by
    simpa +zetaDelta only [biasE, div_one] using hx223
  let x225 : ℝ := biasE c
  have hx225 : Bounds (684382461883 / 1000000000000) (684422976301 / 1000000000000) x225 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx203.1 hx224.2
  let x226 : ℝ := x159⁻¹
  have hx226 : Bounds (5337584171133 / 1000000000000) (5349973047773 / 1000000000000) x226 := by
    apply bounds_inv hx159 <;> norm_num
  let x227 : ℝ := x148*x226
  have hx227 : Bounds (1423507117271 / 1000000000000) (1430174771931 / 1000000000000) x227 := by
    apply bounds_mul hx148 hx226 <;> norm_num
  let x228 : ℝ := x148/x159
  have hx228 : Bounds (1423507117271 / 1000000000000) (1430174771931 / 1000000000000) x228 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx227
  let x229 : ℝ := c*x148
  have hx229 : Bounds (17588536569 / 500000000000) (17670767127 / 500000000000) x229 := by
    apply bounds_mul hc hx148 <;> norm_num
  let x230 : ℝ := x225+x229
  have hx230 : Bounds (719559535021 / 1000000000000) (143952902111 / 200000000000) x230 := by
    apply bounds_add hx225 hx229 <;> norm_num
  let x231 : ℝ := x*x170
  have hx231 : Bounds (17283767773 / 1000000000000) (2170395799 / 125000000000) x231 := by
    apply bounds_mul hx hx170 <;> norm_num
  let x232 : ℝ := x48+x231
  have hx232 : Bounds (693184128019 / 1000000000000) (346670876779 / 500000000000) x232 := by
    apply bounds_add hx48 hx231 <;> norm_num
  let x233 : ℝ := x232⁻¹
  have hx233 : Bounds (288458035267 / 200000000000) (1442618143693 / 1000000000000) x233 := by
    apply bounds_inv hx232 <;> norm_num
  let x234 : ℝ := x230*x233
  have hx234 : Bounds (129726706081 / 125000000000) (1038345342113 / 1000000000000) x234 := by
    apply bounds_mul hx230 hx233 <;> norm_num
  let x235 : ℝ := x230/x232
  have hx235 : Bounds (129726706081 / 125000000000) (1038345342113 / 1000000000000) x235 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx234
  let x236 : ℝ := y*y
  have hx236 : Bounds (341399529 / 10000000000) (34294965721 / 1000000000000) x236 := by
    apply bounds_mul hy hy <;> norm_num
  let x237 : ℝ := -x236
  have hx237 : Bounds (-34294965721 / 1000000000000) (-341399529 / 10000000000) x237 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx236
  let x238 : ℝ := (1 / 1)+x237
  have hx238 : Bounds (965705034279 / 1000000000000) (9658600471 / 10000000000) x238 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx237 <;> norm_num
  let x239 : ℝ := (1 / 1)-x236
  have hx239 : Bounds (965705034279 / 1000000000000) (9658600471 / 10000000000) x239 := by
    exact hx238
  let x240 : ℝ := x239*x159
  have hx240 : Bounds (180506523239 / 1000000000000) (180954532263 / 1000000000000) x240 := by
    apply bounds_mul hx239 hx159 <;> norm_num
  let x241 : ℝ := c*c
  have hx241 : Bounds (1739761 / 100000000) (699126481 / 40000000000) x241 := by
    apply bounds_mul hc hc <;> norm_num
  let x242 : ℝ := -x241
  have hx242 : Bounds (-699126481 / 40000000000) (-1739761 / 100000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx241
  let x243 : ℝ := (1 / 1)+x242
  have hx243 : Bounds (39300873519 / 40000000000) (98260239 / 100000000) x243 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx242 <;> norm_num
  let x244 : ℝ := (1 / 1)-x241
  have hx244 : Bounds (39300873519 / 40000000000) (98260239 / 100000000) x244 := by
    exact hx243
  let x245 : ℝ := x244*x182
  have hx245 : Bounds (86206778383 / 125000000000) (172437761919 / 250000000000) x245 := by
    apply bounds_mul hx244 hx182 <;> norm_num
  let x246 : ℝ := y*y
  have hx246 : Bounds (341399529 / 10000000000) (34294965721 / 1000000000000) x246 := by
    apply bounds_mul hy hy <;> norm_num
  let x247 : ℝ := (1 / 1)+x246
  have hx247 : Bounds (10341399529 / 10000000000) (1034294965721 / 1000000000000) x247 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx246 <;> norm_num
  let x248 : ℝ := x247*x159
  have hx248 : Bounds (38659632251 / 200000000000) (38755172099 / 200000000000) x248 := by
    apply bounds_mul hx247 hx159 <;> norm_num
  let x249 : ℝ := -y
  have hx249 : Bounds (-185189 / 1000000) (-18477 / 100000) x249 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x250 : ℝ := x248+x249
  have hx250 : Bounds (1621832251 / 200000000000) (1801172099 / 200000000000) x250 := by
    apply bounds_add hx248 hx249 <;> norm_num
  let x251 : ℝ := x248-y
  have hx251 : Bounds (1621832251 / 200000000000) (1801172099 / 200000000000) x251 := by
    exact hx250
  let x252 : ℝ := x240*x240
  have hx252 : Bounds (32582604931 / 1000000000000) (32744542747 / 1000000000000) x252 := by
    apply bounds_mul hx240 hx240 <;> norm_num
  let x253 : ℝ := x252⁻¹
  have hx253 : Bounds (30539440044299 / 1000000000000) (30691223188499 / 1000000000000) x253 := by
    apply bounds_inv hx252 <;> norm_num
  let x254 : ℝ := x251*x253
  have hx254 : Bounds (61912310989 / 250000000000) (276400874457 / 1000000000000) x254 := by
    apply bounds_mul hx251 hx253 <;> norm_num
  let x255 : ℝ := x251/x252
  have hx255 : Bounds (61912310989 / 250000000000) (276400874457 / 1000000000000) x255 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx254
  let x256 : ℝ := (-2 / 1)*x255
  have hx256 : Bounds (-276400874457 / 500000000000) (-61912310989 / 125000000000) x256 := by
    apply bounds_mul (bounds_const ((-2 / 1) : ℝ)) hx255 <;> norm_num
  let x257 : ℝ := x256*x228
  have hx257 : Bounds (-790603115177 / 1000000000000) (-176265230679 / 250000000000) x257 := by
    apply bounds_mul hx256 hx228 <;> norm_num
  let x258 : ℝ := (2 / 1)*x182
  have hx258 : Bounds (701922543 / 500000000) (1403927071 / 1000000000) x258 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx182 <;> norm_num
  let x259 : ℝ := c*c
  have hx259 : Bounds (1739761 / 100000000) (699126481 / 40000000000) x259 := by
    apply bounds_mul hc hc <;> norm_num
  let x260 : ℝ := -x259
  have hx260 : Bounds (-699126481 / 40000000000) (-1739761 / 100000000) x260 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx259
  let x261 : ℝ := x258+x260
  have hx261 : Bounds (55454676959 / 40000000000) (1386529461 / 1000000000) x261 := by
    apply bounds_add hx258 hx260 <;> norm_num
  let x262 : ℝ := x258-x259
  have hx262 : Bounds (55454676959 / 40000000000) (1386529461 / 1000000000) x262 := by
    exact hx261
  let x263 : ℝ := c*x262
  have hx263 : Bounds (22857724659 / 125000000000) (5728316481 / 31250000000) x263 := by
    apply bounds_mul hc hx262 <;> norm_num
  let x264 : ℝ := x245*x245
  have hx264 : Bounds (475622952907 / 1000000000000) (475756507771 / 1000000000000) x264 := by
    apply bounds_mul hx245 hx245 <;> norm_num
  let x265 : ℝ := x264⁻¹
  have hx265 : Bounds (2101915546431 / 1000000000000) (2102505764047 / 1000000000000) x265 := by
    apply bounds_inv hx264 <;> norm_num
  let x266 : ℝ := x263*x265
  have hx266 : Bounds (192180027267 / 500000000000) (385402189427 / 1000000000000) x266 := by
    apply bounds_mul hx263 hx265 <;> norm_num
  let x267 : ℝ := x263/x264
  have hx267 : Bounds (192180027267 / 500000000000) (385402189427 / 1000000000000) x267 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx266
  let x268 : ℝ := (2 / 1)*x267
  have hx268 : Bounds (192180027267 / 250000000000) (385402189427 / 500000000000) x268 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx267 <;> norm_num
  let x269 : ℝ := x268*x235
  have hx269 : Bounds (39889411059 / 50000000000) (50022571029 / 62500000000) x269 := by
    apply bounds_mul hx268 hx235 <;> norm_num
  let x270 : ℝ := x257+x269
  have hx270 : Bounds (7185106003 / 1000000000000) (23825053437 / 250000000000) x270 := by
    apply bounds_add hx257 hx269 <;> norm_num
  have hPos : 0 < x270 :=
    lt_of_lt_of_le (by norm_num) hx270.1
  have hBridgeL : doubleCapBridgeL x = x48 := by
    exact hEll'
  rw [← doubleCapBridgeDerivativeTraceForm_eq x]
  simpa +zetaDelta only [doubleCapBridgeDerivativeTraceForm,
    hBridgeL, SmallMean.A, biasB, div_one, pow_two] using hPos

theorem acceptedCell : DoubleCapBridgeDerivativeCellCertificate
    (⟨18, by decide⟩ : Fin 256) doubleCapBridgeDerivativeExpression where
  positive x hx := by
    have hloEq : doubleCapBridgeLo (⟨18, by decide⟩ : Fin 256) =
        (667 / 5120) := by norm_num [doubleCapBridgeLo, doubleCapBridgeStep]
    have hhiEq : doubleCapBridgeHi (⟨18, by decide⟩ : Fin 256) =
        (1337 / 10240) := by norm_num [doubleCapBridgeHi, doubleCapBridgeStep]
    have hlo : (667 / 5120) ≤ x := by
      simpa only [hloEq] using hx.1
    have hhi : x ≤ (1337 / 10240) := by
      simpa only [hhiEq] using hx.2
    exact cell_derivative_pos x ⟨hlo, hhi⟩

#print axioms cell_derivative_pos
#print axioms acceptedCell

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell018

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell019 =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell019
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_derivative_pos (x : ℝ)
    (hx : Bounds (1337 / 10240) (67 / 512) x) :
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
  have hx0 : Bounds (1337 / 5120) (67 / 256) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx <;> norm_num
  let x1 : ℝ := Real.log (2 / 1)
  have hx1 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x1 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x2 : ℝ := Real.log (2 / 1)
  have hx2 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x2 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x3 : ℝ := (1 / 1)+(67 / 256)
  have hx3 : Bounds (323 / 256) (323 / 256) x3 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((67 / 256) : ℝ)) <;> norm_num
  let x4 : ℝ := (1 / 1)+(67 / 256)
  have hx4 : Bounds (323 / 256) (323 / 256) x4 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((67 / 256) : ℝ)) <;> norm_num
  let x5 : ℝ := Real.log x4
  have hx5 : Bounds (116237439 / 500000000) (232474879 / 1000000000) x5 := by
    exact bounds_log hx4 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x6 : ℝ := x3*x5
  have hx6 : Bounds (73329478119 / 250000000000) (293317913739 / 1000000000000) x6 := by
    apply bounds_mul hx3 hx5 <;> norm_num
  let x7 : ℝ := -(67 / 256)
  have hx7 : Bounds (-67 / 256) (-67 / 256) x7 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((67 / 256) : ℝ))
  let x8 : ℝ := (1 / 1)+x7
  have hx8 : Bounds (189 / 256) (189 / 256) x8 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx7 <;> norm_num
  let x9 : ℝ := (1 / 1)-(67 / 256)
  have hx9 : Bounds (189 / 256) (189 / 256) x9 := by
    exact hx8
  let x10 : ℝ := -(67 / 256)
  have hx10 : Bounds (-67 / 256) (-67 / 256) x10 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((67 / 256) : ℝ))
  let x11 : ℝ := (1 / 1)+x10
  have hx11 : Bounds (189 / 256) (189 / 256) x11 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx10 <;> norm_num
  let x12 : ℝ := (1 / 1)-(67 / 256)
  have hx12 : Bounds (189 / 256) (189 / 256) x12 := by
    exact hx11
  let x13 : ℝ := Real.log x12
  have hx13 : Bounds (-30343043 / 100000000) (-303430429 / 1000000000) x13 := by
    exact bounds_log hx12 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x14 : ℝ := x9*x13
  have hx14 : Bounds (-224016997149 / 1000000000000) (-22401699641 / 100000000000) x14 := by
    apply bounds_mul hx9 hx13 <;> norm_num
  let x15 : ℝ := x6+x14
  have hx15 : Bounds (69300915327 / 1000000000000) (69300917329 / 1000000000000) x15 := by
    apply bounds_add hx6 hx14 <;> norm_num
  let x16 : ℝ := (2 / 1)⁻¹
  have hx16 : Bounds (1 / 2) (1 / 2) x16 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x17 : ℝ := x15*x16
  have hx17 : Bounds (34650457663 / 1000000000000) (6930091733 / 200000000000) x17 := by
    apply bounds_mul hx15 hx16 <;> norm_num
  let x18 : ℝ := x15/(2 / 1)
  have hx18 : Bounds (34650457663 / 1000000000000) (6930091733 / 200000000000) x18 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx17
  let x19 : ℝ := -x18
  have hx19 : Bounds (-6930091733 / 200000000000) (-34650457663 / 1000000000000) x19 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx18
  let x20 : ℝ := x2+x19
  have hx20 : Bounds (131699344267 / 200000000000) (658496723337 / 1000000000000) x20 := by
    apply bounds_add hx2 hx19 <;> norm_num
  let x21 : ℝ := x2-x18
  have hx21 : Bounds (131699344267 / 200000000000) (658496723337 / 1000000000000) x21 := by
    exact hx20
  let x22 : ℝ := biasE (67 / 256)
  have hx22 : Bounds (131699344267 / 200000000000) (658496723337 / 1000000000000) x22 := by
    simpa +zetaDelta only [biasE, div_one] using hx21
  let x23 : ℝ := Real.log (2 / 1)
  have hx23 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x23 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x24 : ℝ := (1 / 1)+(1337 / 5120)
  have hx24 : Bounds (6457 / 5120) (6457 / 5120) x24 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1337 / 5120) : ℝ)) <;> norm_num
  let x25 : ℝ := (1 / 1)+(1337 / 5120)
  have hx25 : Bounds (6457 / 5120) (6457 / 5120) x25 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1337 / 5120) : ℝ)) <;> norm_num
  let x26 : ℝ := Real.log x25
  have hx26 : Bounds (116005187 / 500000000) (1856083 / 8000000) x26 := by
    exact bounds_log hx25 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x27 : ℝ := x24*x26
  have hx27 : Bounds (292595895491 / 1000000000000) (292595896753 / 1000000000000) x27 := by
    apply bounds_mul hx24 hx26 <;> norm_num
  let x28 : ℝ := -(1337 / 5120)
  have hx28 : Bounds (-1337 / 5120) (-1337 / 5120) x28 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1337 / 5120) : ℝ))
  let x29 : ℝ := (1 / 1)+x28
  have hx29 : Bounds (3783 / 5120) (3783 / 5120) x29 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx28 <;> norm_num
  let x30 : ℝ := (1 / 1)-(1337 / 5120)
  have hx30 : Bounds (3783 / 5120) (3783 / 5120) x30 := by
    exact hx29
  let x31 : ℝ := -(1337 / 5120)
  have hx31 : Bounds (-1337 / 5120) (-1337 / 5120) x31 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1337 / 5120) : ℝ))
  let x32 : ℝ := (1 / 1)+x31
  have hx32 : Bounds (3783 / 5120) (3783 / 5120) x32 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx31 <;> norm_num
  let x33 : ℝ := (1 / 1)-(1337 / 5120)
  have hx33 : Bounds (3783 / 5120) (3783 / 5120) x33 := by
    exact hx32
  let x34 : ℝ := Real.log x33
  have hx34 : Bounds (-151318547 / 500000000) (-302637093 / 1000000000) x34 := by
    exact bounds_log hx33 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x35 : ℝ := x30*x34
  have hx35 : Bounds (-223608618477 / 1000000000000) (-111804308869 / 500000000000) x35 := by
    apply bounds_mul hx30 hx34 <;> norm_num
  let x36 : ℝ := x27+x35
  have hx36 : Bounds (34493638507 / 500000000000) (13797455803 / 200000000000) x36 := by
    apply bounds_add hx27 hx35 <;> norm_num
  let x37 : ℝ := (2 / 1)⁻¹
  have hx37 : Bounds (1 / 2) (1 / 2) x37 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x38 : ℝ := x36*x37
  have hx38 : Bounds (34493638507 / 1000000000000) (8623409877 / 250000000000) x38 := by
    apply bounds_mul hx36 hx37 <;> norm_num
  let x39 : ℝ := x36/(2 / 1)
  have hx39 : Bounds (34493638507 / 1000000000000) (8623409877 / 250000000000) x39 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx38
  let x40 : ℝ := -x39
  have hx40 : Bounds (-8623409877 / 250000000000) (-34493638507 / 1000000000000) x40 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx39
  let x41 : ℝ := x23+x40
  have hx41 : Bounds (164663385123 / 250000000000) (658653542493 / 1000000000000) x41 := by
    apply bounds_add hx23 hx40 <;> norm_num
  let x42 : ℝ := x23-x39
  have hx42 : Bounds (164663385123 / 250000000000) (658653542493 / 1000000000000) x42 := by
    exact hx41
  let x43 : ℝ := biasE (1337 / 5120)
  have hx43 : Bounds (164663385123 / 250000000000) (658653542493 / 1000000000000) x43 := by
    simpa +zetaDelta only [biasE, div_one] using hx42
  let x44 : ℝ := biasE x0
  have hx44 : Bounds (131699344267 / 200000000000) (658653542493 / 1000000000000) x44 := by
    exact bounds_biasE hx0 (by norm_num) (by norm_num) hx22.1 hx43.2
  let x45 : ℝ := x1+x44
  have hx45 : Bounds (270328780267 / 200000000000) (1351800723493 / 1000000000000) x45 := by
    apply bounds_add hx1 hx44 <;> norm_num
  let x46 : ℝ := (2 / 1)⁻¹
  have hx46 : Bounds (1 / 2) (1 / 2) x46 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x47 : ℝ := x45*x46
  have hx47 : Bounds (675821950667 / 1000000000000) (675900361747 / 1000000000000) x47 := by
    apply bounds_mul hx45 hx46 <;> norm_num
  let x48 : ℝ := x45/(2 / 1)
  have hx48 : Bounds (675821950667 / 1000000000000) (675900361747 / 1000000000000) x48 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx47
  let x49 : ℝ := Real.log (2 / 1)
  have hx49 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x49 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x50 : ℝ := (1 / 1)+(46297 / 250000)
  have hx50 : Bounds (296297 / 250000) (296297 / 250000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((46297 / 250000) : ℝ)) <;> norm_num
  let x51 : ℝ := (1 / 1)+(46297 / 250000)
  have hx51 : Bounds (296297 / 250000) (296297 / 250000) x51 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((46297 / 250000) : ℝ)) <;> norm_num
  let x52 : ℝ := Real.log x51
  have hx52 : Bounds (169901411 / 1000000000) (42475353 / 250000000) x52 := by
    exact bounds_log hx51 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x53 : ℝ := x50*x52
  have hx53 : Bounds (402730227 / 2000000000) (100682557343 / 500000000000) x53 := by
    apply bounds_mul hx50 hx52 <;> norm_num
  let x54 : ℝ := -(46297 / 250000)
  have hx54 : Bounds (-46297 / 250000) (-46297 / 250000) x54 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((46297 / 250000) : ℝ))
  let x55 : ℝ := (1 / 1)+x54
  have hx55 : Bounds (203703 / 250000) (203703 / 250000) x55 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx54 <;> norm_num
  let x56 : ℝ := (1 / 1)-(46297 / 250000)
  have hx56 : Bounds (203703 / 250000) (203703 / 250000) x56 := by
    exact hx55
  let x57 : ℝ := -(46297 / 250000)
  have hx57 : Bounds (-46297 / 250000) (-46297 / 250000) x57 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((46297 / 250000) : ℝ))
  let x58 : ℝ := (1 / 1)+x57
  have hx58 : Bounds (203703 / 250000) (203703 / 250000) x58 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx57 <;> norm_num
  let x59 : ℝ := (1 / 1)-(46297 / 250000)
  have hx59 : Bounds (203703 / 250000) (203703 / 250000) x59 := by
    exact hx58
  let x60 : ℝ := Real.log x59
  have hx60 : Bounds (-51199467 / 250000000) (-204797867 / 1000000000) x60 := by
    exact bounds_log hx59 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x61 : ℝ := x56*x60
  have hx61 : Bounds (-166871760421 / 1000000000000) (-83435879803 / 500000000000) x61 := by
    apply bounds_mul hx56 hx60 <;> norm_num
  let x62 : ℝ := x53+x61
  have hx62 : Bounds (34493353079 / 1000000000000) (862333877 / 25000000000) x62 := by
    apply bounds_add hx53 hx61 <;> norm_num
  let x63 : ℝ := (2 / 1)⁻¹
  have hx63 : Bounds (1 / 2) (1 / 2) x63 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x64 : ℝ := x62*x63
  have hx64 : Bounds (17246676539 / 1000000000000) (862333877 / 50000000000) x64 := by
    apply bounds_mul hx62 hx63 <;> norm_num
  let x65 : ℝ := x62/(2 / 1)
  have hx65 : Bounds (17246676539 / 1000000000000) (862333877 / 50000000000) x65 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx64
  let x66 : ℝ := -x65
  have hx66 : Bounds (-862333877 / 50000000000) (-17246676539 / 1000000000000) x66 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx65
  let x67 : ℝ := x49+x66
  have hx67 : Bounds (33795025123 / 50000000000) (675900504461 / 1000000000000) x67 := by
    apply bounds_add hx49 hx66 <;> norm_num
  let x68 : ℝ := x49-x65
  have hx68 : Bounds (33795025123 / 50000000000) (675900504461 / 1000000000000) x68 := by
    exact hx67
  let x69 : ℝ := biasE (46297 / 250000)
  have hx69 : Bounds (33795025123 / 50000000000) (675900504461 / 1000000000000) x69 := by
    simpa +zetaDelta only [biasE, div_one] using hx68
  let x70 : ℝ := Real.log (2 / 1)
  have hx70 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x70 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x71 : ℝ := (1 / 1)+(185607 / 1000000)
  have hx71 : Bounds (1185607 / 1000000) (1185607 / 1000000) x71 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((185607 / 1000000) : ℝ)) <;> norm_num
  let x72 : ℝ := (1 / 1)+(185607 / 1000000)
  have hx72 : Bounds (1185607 / 1000000) (1185607 / 1000000) x72 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((185607 / 1000000) : ℝ)) <;> norm_num
  let x73 : ℝ := Real.log x72
  have hx73 : Bounds (170254879 / 1000000000) (1064093 / 6250000) x73 := by
    exact bounds_log hx72 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x74 : ℝ := x71*x73
  have hx74 : Bounds (100927688163 / 500000000000) (201855377513 / 1000000000000) x74 := by
    apply bounds_mul hx71 hx73 <;> norm_num
  let x75 : ℝ := -(185607 / 1000000)
  have hx75 : Bounds (-185607 / 1000000) (-185607 / 1000000) x75 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((185607 / 1000000) : ℝ))
  let x76 : ℝ := (1 / 1)+x75
  have hx76 : Bounds (814393 / 1000000) (814393 / 1000000) x76 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx75 <;> norm_num
  let x77 : ℝ := (1 / 1)-(185607 / 1000000)
  have hx77 : Bounds (814393 / 1000000) (814393 / 1000000) x77 := by
    exact hx76
  let x78 : ℝ := -(185607 / 1000000)
  have hx78 : Bounds (-185607 / 1000000) (-185607 / 1000000) x78 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((185607 / 1000000) : ℝ))
  let x79 : ℝ := (1 / 1)+x78
  have hx79 : Bounds (814393 / 1000000) (814393 / 1000000) x79 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx78 <;> norm_num
  let x80 : ℝ := (1 / 1)-(185607 / 1000000)
  have hx80 : Bounds (814393 / 1000000) (814393 / 1000000) x80 := by
    exact hx79
  let x81 : ℝ := Real.log x80
  have hx81 : Bounds (-205312229 / 1000000000) (-51328057 / 250000000) x81 := by
    exact bounds_log hx80 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x82 : ℝ := x77*x81
  have hx82 : Bounds (-1306287829 / 7812500000) (-167204841297 / 1000000000000) x82 := by
    apply bounds_mul hx77 hx81 <;> norm_num
  let x83 : ℝ := x74+x82
  have hx83 : Bounds (17325267107 / 500000000000) (4331317027 / 125000000000) x83 := by
    apply bounds_add hx74 hx82 <;> norm_num
  let x84 : ℝ := (2 / 1)⁻¹
  have hx84 : Bounds (1 / 2) (1 / 2) x84 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x85 : ℝ := x83*x84
  have hx85 : Bounds (17325267107 / 1000000000000) (4331317027 / 250000000000) x85 := by
    apply bounds_mul hx83 hx84 <;> norm_num
  let x86 : ℝ := x83/(2 / 1)
  have hx86 : Bounds (17325267107 / 1000000000000) (4331317027 / 250000000000) x86 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx85
  let x87 : ℝ := -x86
  have hx87 : Bounds (-4331317027 / 250000000000) (-17325267107 / 1000000000000) x87 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx86
  let x88 : ℝ := x70+x87
  have hx88 : Bounds (168955477973 / 250000000000) (675821913893 / 1000000000000) x88 := by
    apply bounds_add hx70 hx87 <;> norm_num
  let x89 : ℝ := x70-x86
  have hx89 : Bounds (168955477973 / 250000000000) (675821913893 / 1000000000000) x89 := by
    exact hx88
  let x90 : ℝ := biasE (185607 / 1000000)
  have hx90 : Bounds (168955477973 / 250000000000) (675821913893 / 1000000000000) x90 := by
    simpa +zetaDelta only [biasE, div_one] using hx89
  let y : ℝ := doubleCapHighTailY x
  have hEll' : Real.log 2 * doubleCapHighTailFloor x = x48 := by
    simpa +zetaDelta only [div_one] using hEll
  have hy : Bounds (46297 / 250000) (185607 / 1000000) y := by
    dsimp only [y, doubleCapHighTailY]
    apply entropyInverseBias_bracket hh0.le hh1.le
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (185607 / 1000000) ≤ (675821913893 / 1000000000000) := hx90.2
      have h2 : (675821950667 / 1000000000000) ≤ x48 := hx48.1
      linarith [hEll']
    · have h1 : x48 ≤ (675900361747 / 1000000000000) := hx48.2
      have h2 : (33795025123 / 50000000000) ≤ biasE (46297 / 250000) := hx69.1
      linarith [hEll']
  let x91 : ℝ := x⁻¹
  have hx91 : Bounds (955223880597 / 125000000000) (7658937920719 / 1000000000000) x91 := by
    apply bounds_inv hx <;> norm_num
  let x92 : ℝ := x48*x91
  have hx92 : Bounds (516449013047 / 100000000000) (1294169727803 / 250000000000) x92 := by
    apply bounds_mul hx48 hx91 <;> norm_num
  let x93 : ℝ := x48/x
  have hx93 : Bounds (516449013047 / 100000000000) (1294169727803 / 250000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(33051 / 250000)
  have hx95 : Bounds (283051 / 250000) (283051 / 250000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((33051 / 250000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(33051 / 250000)
  have hx96 : Bounds (283051 / 250000) (283051 / 250000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((33051 / 250000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (4966647 / 40000000) (3880193 / 31250000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (140581439999 / 1000000000000) (35145360283 / 250000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(33051 / 250000)
  have hx99 : Bounds (-33051 / 250000) (-33051 / 250000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((33051 / 250000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (216949 / 250000) (216949 / 250000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(33051 / 250000)
  have hx101 : Bounds (216949 / 250000) (216949 / 250000) x101 := by
    exact hx100
  let x102 : ℝ := -(33051 / 250000)
  have hx102 : Bounds (-33051 / 250000) (-33051 / 250000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((33051 / 250000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (216949 / 250000) (216949 / 250000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(33051 / 250000)
  have hx104 : Bounds (216949 / 250000) (216949 / 250000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-28359723 / 200000000) (-70899307 / 500000000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-123052270903 / 1000000000000) (-61526135017 / 500000000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (2191146137 / 125000000000) (8764585549 / 500000000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (2191146137 / 250000000000) (8764585549 / 1000000000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (2191146137 / 250000000000) (8764585549 / 1000000000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-8764585549 / 1000000000000) (-2191146137 / 250000000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (684382594451 / 1000000000000) (171095649113 / 250000000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (684382594451 / 1000000000000) (171095649113 / 250000000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (33051 / 250000)
  have hx114 : Bounds (684382594451 / 1000000000000) (171095649113 / 250000000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(13251 / 100000)
  have hx116 : Bounds (113251 / 100000) (113251 / 100000) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((13251 / 100000) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(13251 / 100000)
  have hx117 : Bounds (113251 / 100000) (113251 / 100000) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((13251 / 100000) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (15554551 / 125000000) (124436409 / 1000000000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (17615684553 / 125000000000) (140925477557 / 1000000000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(13251 / 100000)
  have hx120 : Bounds (-13251 / 100000) (-13251 / 100000) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((13251 / 100000) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (86749 / 100000) (86749 / 100000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(13251 / 100000)
  have hx122 : Bounds (86749 / 100000) (86749 / 100000) x122 := by
    exact hx121
  let x123 : ℝ := -(13251 / 100000)
  have hx123 : Bounds (-13251 / 100000) (-13251 / 100000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((13251 / 100000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (86749 / 100000) (86749 / 100000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(13251 / 100000)
  have hx125 : Bounds (86749 / 100000) (86749 / 100000) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-28430259 / 200000000) (-71075647 / 500000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-1233148269 / 10000000000) (-7707176627 / 62500000000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (4402662381 / 250000000000) (704426061 / 40000000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (4402662381 / 500000000000) (8805325763 / 1000000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (4402662381 / 500000000000) (8805325763 / 1000000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-8805325763 / 1000000000000) (-4402662381 / 500000000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (684341854237 / 1000000000000) (342170928119 / 500000000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (684341854237 / 1000000000000) (342170928119 / 500000000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (13251 / 100000)
  have hx135 : Bounds (684341854237 / 1000000000000) (342170928119 / 500000000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(33051 / 250000)
  have hx136 : Bounds (85345781651 / 125000000000) (342188829389 / 500000000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((33051 / 250000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(13251 / 100000)
  have hx137 : Bounds (171086646797 / 250000000000) (27438468901 / 40000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((13251 / 100000) : ℝ)) <;> norm_num
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
  have hc : Bounds (33051 / 250000) (13251 / 100000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num)
      (by norm_num) (show 0 < x93 by linarith [hx93.1]) hcEq
    · have h1 : x93 * (33051 / 250000) ≤ (342188829389 / 500000000000) := hx136.2
      have h2 : (684382594451 / 1000000000000) ≤ biasE (33051 / 250000) := hx114.1
      linarith
    · have h1 : biasE (13251 / 100000) ≤ (342170928119 / 500000000000) := hx135.2
      have h2 : (171086646797 / 250000000000) ≤ x93 * (13251 / 100000) := hx137.1
      linarith
  let x138 : ℝ := (1 / 1)+x0
  have hx138 : Bounds (6457 / 5120) (323 / 256) x138 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx0 <;> norm_num
  let x139 : ℝ := -x0
  have hx139 : Bounds (-67 / 256) (-1337 / 5120) x139 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x140 : ℝ := (1 / 1)+x139
  have hx140 : Bounds (189 / 256) (3783 / 5120) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx139 <;> norm_num
  let x141 : ℝ := (1 / 1)-x0
  have hx141 : Bounds (189 / 256) (3783 / 5120) x141 := by
    exact hx140
  let x142 : ℝ := x141⁻¹
  have hx142 : Bounds (1353423209093 / 1000000000000) (677248677249 / 500000000000) x142 := by
    apply bounds_inv hx141 <;> norm_num
  let x143 : ℝ := x138*x142
  have hx143 : Bounds (853423209093 / 500000000000) (427248677249 / 250000000000) x143 := by
    apply bounds_mul hx138 hx142 <;> norm_num
  let x144 : ℝ := x138/x141
  have hx144 : Bounds (853423209093 / 500000000000) (427248677249 / 250000000000) x144 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx143
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (534647467 / 1000000000) (535905309 / 1000000000) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_14.2)
  let x146 : ℝ := (2 / 1)⁻¹
  have hx146 : Bounds (1 / 2) (1 / 2) x146 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x147 : ℝ := x145*x146
  have hx147 : Bounds (534647467 / 2000000000) (535905309 / 2000000000) x147 := by
    apply bounds_mul hx145 hx146 <;> norm_num
  let x148 : ℝ := x145/(2 / 1)
  have hx148 : Bounds (534647467 / 2000000000) (535905309 / 2000000000) x148 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx147
  let x149 : ℝ := (1 / 1)+y
  have hx149 : Bounds (296297 / 250000) (1185607 / 1000000) x149 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x150 : ℝ := -y
  have hx150 : Bounds (-185607 / 1000000) (-46297 / 250000) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (814393 / 1000000) (203703 / 250000) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-y
  have hx152 : Bounds (814393 / 1000000) (203703 / 250000) x152 := by
    exact hx151
  let x153 : ℝ := x152⁻¹
  have hx153 : Bounds (306819241739 / 250000000000) (1227908393123 / 1000000000000) x153 := by
    apply bounds_inv hx152 <;> norm_num
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (181819241739 / 125000000000) (727908393123 / 500000000000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x149/x152
  have hx155 : Bounds (181819241739 / 125000000000) (727908393123 / 500000000000) x155 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx154
  let x156 : ℝ := Real.log x155
  have hx156 : Bounds (187349639 / 500000000) (375567109 / 1000000000) x156 := by
    exact bounds_log hx155 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_16.2)
  let x157 : ℝ := (2 / 1)⁻¹
  have hx157 : Bounds (1 / 2) (1 / 2) x157 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x158 : ℝ := x156*x157
  have hx158 : Bounds (187349639 / 1000000000) (375567109 / 2000000000) x158 := by
    apply bounds_mul hx156 hx157 <;> norm_num
  let x159 : ℝ := x156/(2 / 1)
  have hx159 : Bounds (187349639 / 1000000000) (375567109 / 2000000000) x159 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx158
  let x160 : ℝ := (1 / 1)+c
  have hx160 : Bounds (283051 / 250000) (113251 / 100000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x161 : ℝ := -c
  have hx161 : Bounds (-13251 / 100000) (-33051 / 250000) x161 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x162 : ℝ := (1 / 1)+x161
  have hx162 : Bounds (86749 / 100000) (216949 / 250000) x162 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx161 <;> norm_num
  let x163 : ℝ := (1 / 1)-c
  have hx163 : Bounds (86749 / 100000) (216949 / 250000) x163 := by
    exact hx162
  let x164 : ℝ := x163⁻¹
  have hx164 : Bounds (576172280121 / 500000000000) (576375520179 / 500000000000) x164 := by
    apply bounds_inv hx163 <;> norm_num
  let x165 : ℝ := x160*x164
  have hx165 : Bounds (326172280121 / 250000000000) (326375520179 / 250000000000) x165 := by
    apply bounds_mul hx160 hx164 <;> norm_num
  let x166 : ℝ := x160/x163
  have hx166 : Bounds (326172280121 / 250000000000) (326375520179 / 250000000000) x166 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx165
  let x167 : ℝ := Real.log x166
  have hx167 : Bounds (26596479 / 100000000) (266587703 / 1000000000) x167 := by
    exact bounds_log hx166 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x168 : ℝ := (2 / 1)⁻¹
  have hx168 : Bounds (1 / 2) (1 / 2) x168 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x169 : ℝ := x167*x168
  have hx169 : Bounds (26596479 / 200000000) (266587703 / 2000000000) x169 := by
    apply bounds_mul hx167 hx168 <;> norm_num
  let x170 : ℝ := x167/(2 / 1)
  have hx170 : Bounds (26596479 / 200000000) (266587703 / 2000000000) x170 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx169
  let x171 : ℝ := Real.log (2 / 1)
  have hx171 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x171 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x172 : ℝ := c*c
  have hx172 : Bounds (1092368601 / 62500000000) (175589001 / 10000000000) x172 := by
    apply bounds_mul hc hc <;> norm_num
  let x173 : ℝ := -x172
  have hx173 : Bounds (-175589001 / 10000000000) (-1092368601 / 62500000000) x173 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx172
  let x174 : ℝ := (1 / 1)+x173
  have hx174 : Bounds (9824410999 / 10000000000) (61407631399 / 62500000000) x174 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx173 <;> norm_num
  let x175 : ℝ := (1 / 1)-x172
  have hx175 : Bounds (9824410999 / 10000000000) (61407631399 / 62500000000) x175 := by
    exact hx174
  let x176 : ℝ := Real.log x175
  have hx176 : Bounds (-17714887 / 1000000000) (-17632439 / 1000000000) x176 := by
    exact bounds_log hx175 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (-17714887 / 2000000000) (-17632439 / 2000000000) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (-17714887 / 2000000000) (-17632439 / 2000000000) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (17632439 / 2000000000) (17714887 / 2000000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x171+x180
  have hx181 : Bounds (1403926799 / 2000000000) (1404009249 / 2000000000) x181 := by
    apply bounds_add hx171 hx180 <;> norm_num
  let x182 : ℝ := x171-x179
  have hx182 : Bounds (1403926799 / 2000000000) (1404009249 / 2000000000) x182 := by
    exact hx181
  let x183 : ℝ := Real.log (2 / 1)
  have hx183 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x183 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x184 : ℝ := (1 / 1)+(13251 / 100000)
  have hx184 : Bounds (113251 / 100000) (113251 / 100000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((13251 / 100000) : ℝ)) <;> norm_num
  let x185 : ℝ := (1 / 1)+(13251 / 100000)
  have hx185 : Bounds (113251 / 100000) (113251 / 100000) x185 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((13251 / 100000) : ℝ)) <;> norm_num
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (15554551 / 125000000) (124436409 / 1000000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x187 : ℝ := x184*x186
  have hx187 : Bounds (17615684553 / 125000000000) (140925477557 / 1000000000000) x187 := by
    apply bounds_mul hx184 hx186 <;> norm_num
  let x188 : ℝ := -(13251 / 100000)
  have hx188 : Bounds (-13251 / 100000) (-13251 / 100000) x188 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((13251 / 100000) : ℝ))
  let x189 : ℝ := (1 / 1)+x188
  have hx189 : Bounds (86749 / 100000) (86749 / 100000) x189 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx188 <;> norm_num
  let x190 : ℝ := (1 / 1)-(13251 / 100000)
  have hx190 : Bounds (86749 / 100000) (86749 / 100000) x190 := by
    exact hx189
  let x191 : ℝ := -(13251 / 100000)
  have hx191 : Bounds (-13251 / 100000) (-13251 / 100000) x191 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((13251 / 100000) : ℝ))
  let x192 : ℝ := (1 / 1)+x191
  have hx192 : Bounds (86749 / 100000) (86749 / 100000) x192 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx191 <;> norm_num
  let x193 : ℝ := (1 / 1)-(13251 / 100000)
  have hx193 : Bounds (86749 / 100000) (86749 / 100000) x193 := by
    exact hx192
  let x194 : ℝ := Real.log x193
  have hx194 : Bounds (-28430259 / 200000000) (-71075647 / 500000000) x194 := by
    exact bounds_log hx193 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x195 : ℝ := x190*x194
  have hx195 : Bounds (-1233148269 / 10000000000) (-7707176627 / 62500000000) x195 := by
    apply bounds_mul hx190 hx194 <;> norm_num
  let x196 : ℝ := x187+x195
  have hx196 : Bounds (4402662381 / 250000000000) (704426061 / 40000000000) x196 := by
    apply bounds_add hx187 hx195 <;> norm_num
  let x197 : ℝ := (2 / 1)⁻¹
  have hx197 : Bounds (1 / 2) (1 / 2) x197 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x198 : ℝ := x196*x197
  have hx198 : Bounds (4402662381 / 500000000000) (8805325763 / 1000000000000) x198 := by
    apply bounds_mul hx196 hx197 <;> norm_num
  let x199 : ℝ := x196/(2 / 1)
  have hx199 : Bounds (4402662381 / 500000000000) (8805325763 / 1000000000000) x199 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx198
  let x200 : ℝ := -x199
  have hx200 : Bounds (-8805325763 / 1000000000000) (-4402662381 / 500000000000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx199
  let x201 : ℝ := x183+x200
  have hx201 : Bounds (684341854237 / 1000000000000) (342170928119 / 500000000000) x201 := by
    apply bounds_add hx183 hx200 <;> norm_num
  let x202 : ℝ := x183-x199
  have hx202 : Bounds (684341854237 / 1000000000000) (342170928119 / 500000000000) x202 := by
    exact hx201
  let x203 : ℝ := biasE (13251 / 100000)
  have hx203 : Bounds (684341854237 / 1000000000000) (342170928119 / 500000000000) x203 := by
    simpa +zetaDelta only [biasE, div_one] using hx202
  let x204 : ℝ := Real.log (2 / 1)
  have hx204 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x204 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x205 : ℝ := (1 / 1)+(33051 / 250000)
  have hx205 : Bounds (283051 / 250000) (283051 / 250000) x205 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((33051 / 250000) : ℝ)) <;> norm_num
  let x206 : ℝ := (1 / 1)+(33051 / 250000)
  have hx206 : Bounds (283051 / 250000) (283051 / 250000) x206 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((33051 / 250000) : ℝ)) <;> norm_num
  let x207 : ℝ := Real.log x206
  have hx207 : Bounds (4966647 / 40000000) (3880193 / 31250000) x207 := by
    exact bounds_log hx206 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x208 : ℝ := x205*x207
  have hx208 : Bounds (140581439999 / 1000000000000) (35145360283 / 250000000000) x208 := by
    apply bounds_mul hx205 hx207 <;> norm_num
  let x209 : ℝ := -(33051 / 250000)
  have hx209 : Bounds (-33051 / 250000) (-33051 / 250000) x209 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((33051 / 250000) : ℝ))
  let x210 : ℝ := (1 / 1)+x209
  have hx210 : Bounds (216949 / 250000) (216949 / 250000) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx209 <;> norm_num
  let x211 : ℝ := (1 / 1)-(33051 / 250000)
  have hx211 : Bounds (216949 / 250000) (216949 / 250000) x211 := by
    exact hx210
  let x212 : ℝ := -(33051 / 250000)
  have hx212 : Bounds (-33051 / 250000) (-33051 / 250000) x212 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((33051 / 250000) : ℝ))
  let x213 : ℝ := (1 / 1)+x212
  have hx213 : Bounds (216949 / 250000) (216949 / 250000) x213 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx212 <;> norm_num
  let x214 : ℝ := (1 / 1)-(33051 / 250000)
  have hx214 : Bounds (216949 / 250000) (216949 / 250000) x214 := by
    exact hx213
  let x215 : ℝ := Real.log x214
  have hx215 : Bounds (-28359723 / 200000000) (-70899307 / 500000000) x215 := by
    exact bounds_log hx214 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x216 : ℝ := x211*x215
  have hx216 : Bounds (-123052270903 / 1000000000000) (-61526135017 / 500000000000) x216 := by
    apply bounds_mul hx211 hx215 <;> norm_num
  let x217 : ℝ := x208+x216
  have hx217 : Bounds (2191146137 / 125000000000) (8764585549 / 500000000000) x217 := by
    apply bounds_add hx208 hx216 <;> norm_num
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (2191146137 / 250000000000) (8764585549 / 1000000000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (2191146137 / 250000000000) (8764585549 / 1000000000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := -x220
  have hx221 : Bounds (-8764585549 / 1000000000000) (-2191146137 / 250000000000) x221 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx220
  let x222 : ℝ := x204+x221
  have hx222 : Bounds (684382594451 / 1000000000000) (171095649113 / 250000000000) x222 := by
    apply bounds_add hx204 hx221 <;> norm_num
  let x223 : ℝ := x204-x220
  have hx223 : Bounds (684382594451 / 1000000000000) (171095649113 / 250000000000) x223 := by
    exact hx222
  let x224 : ℝ := biasE (33051 / 250000)
  have hx224 : Bounds (684382594451 / 1000000000000) (171095649113 / 250000000000) x224 := by
    simpa +zetaDelta only [biasE, div_one] using hx223
  let x225 : ℝ := biasE c
  have hx225 : Bounds (684341854237 / 1000000000000) (171095649113 / 250000000000) x225 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx203.1 hx224.2
  let x226 : ℝ := x159⁻¹
  have hx226 : Bounds (5325279962149 / 1000000000000) (266880685049 / 50000000000) x226 := by
    apply bounds_inv hx159 <;> norm_num
  let x227 : ℝ := x148*x226
  have hx227 : Bounds (711786860707 / 500000000000) (715113879937 / 500000000000) x227 := by
    apply bounds_mul hx148 hx226 <;> norm_num
  let x228 : ℝ := x148/x159
  have hx228 : Bounds (711786860707 / 500000000000) (715113879937 / 500000000000) x228 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx227
  let x229 : ℝ := c*x148
  have hx229 : Bounds (35341266863 / 1000000000000) (4438300781 / 125000000000) x229 := by
    apply bounds_mul hc hx148 <;> norm_num
  let x230 : ℝ := x225+x229
  have hx230 : Bounds (7196831211 / 10000000000) (7198890027 / 10000000000) x230 := by
    apply bounds_add hx225 hx229 <;> norm_num
  let x231 : ℝ := x*x170
  have hx231 : Bounds (17363033409 / 1000000000000) (17442750099 / 1000000000000) x231 := by
    apply bounds_mul hx hx170 <;> norm_num
  let x232 : ℝ := x48+x231
  have hx232 : Bounds (173296246019 / 250000000000) (346671555923 / 500000000000) x232 := by
    apply bounds_add hx48 hx231 <;> norm_num
  let x233 : ℝ := x232⁻¹
  have hx233 : Bounds (1442287350829 / 1000000000000) (288523272423 / 200000000000) x233 := by
    apply bounds_inv hx232 <;> norm_num
  let x234 : ℝ := x230*x233
  have hx234 : Bounds (1037989862167 / 1000000000000) (519261827101 / 500000000000) x234 := by
    apply bounds_mul hx230 hx233 <;> norm_num
  let x235 : ℝ := x230/x232
  have hx235 : Bounds (1037989862167 / 1000000000000) (519261827101 / 500000000000) x235 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx234
  let x236 : ℝ := y*y
  have hx236 : Bounds (2143412209 / 62500000000) (34449958449 / 1000000000000) x236 := by
    apply bounds_mul hy hy <;> norm_num
  let x237 : ℝ := -x236
  have hx237 : Bounds (-34449958449 / 1000000000000) (-2143412209 / 62500000000) x237 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx236
  let x238 : ℝ := (1 / 1)+x237
  have hx238 : Bounds (965550041551 / 1000000000000) (60356587791 / 62500000000) x238 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx237 <;> norm_num
  let x239 : ℝ := (1 / 1)-x236
  have hx239 : Bounds (965550041551 / 1000000000000) (60356587791 / 62500000000) x239 := by
    exact hx238
  let x240 : ℝ := x239*x159
  have hx240 : Bounds (180895451721 / 1000000000000) (181343593487 / 1000000000000) x240 := by
    apply bounds_mul hx239 hx159 <;> norm_num
  let x241 : ℝ := c*c
  have hx241 : Bounds (1092368601 / 62500000000) (175589001 / 10000000000) x241 := by
    apply bounds_mul hc hc <;> norm_num
  let x242 : ℝ := -x241
  have hx242 : Bounds (-175589001 / 10000000000) (-1092368601 / 62500000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx241
  let x243 : ℝ := (1 / 1)+x242
  have hx243 : Bounds (9824410999 / 10000000000) (61407631399 / 62500000000) x243 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx242 <;> norm_num
  let x244 : ℝ := (1 / 1)-x241
  have hx244 : Bounds (9824410999 / 10000000000) (61407631399 / 62500000000) x244 := by
    exact hx243
  let x245 : ℝ := x244*x182
  have hx245 : Bounds (344818847147 / 500000000000) (172433764887 / 250000000000) x245 := by
    apply bounds_mul hx244 hx182 <;> norm_num
  let x246 : ℝ := y*y
  have hx246 : Bounds (2143412209 / 62500000000) (34449958449 / 1000000000000) x246 := by
    apply bounds_mul hy hy <;> norm_num
  let x247 : ℝ := (1 / 1)+x246
  have hx247 : Bounds (64643412209 / 62500000000) (1034449958449 / 1000000000000) x247 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx246 <;> norm_num
  let x248 : ℝ := x247*x159
  have hx248 : Bounds (193774719057 / 1000000000000) (3885053803 / 20000000000) x248 := by
    apply bounds_mul hx247 hx159 <;> norm_num
  let x249 : ℝ := -y
  have hx249 : Bounds (-185607 / 1000000) (-46297 / 250000) x249 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x250 : ℝ := x248+x249
  have hx250 : Bounds (8167719057 / 1000000000000) (181293803 / 20000000000) x250 := by
    apply bounds_add hx248 hx249 <;> norm_num
  let x251 : ℝ := x248-y
  have hx251 : Bounds (8167719057 / 1000000000000) (181293803 / 20000000000) x251 := by
    exact hx250
  let x252 : ℝ := x240*x240
  have hx252 : Bounds (32723164453 / 1000000000000) (32885498899 / 1000000000000) x252 := by
    apply bounds_mul hx240 hx240 <;> norm_num
  let x253 : ℝ := x252⁻¹
  have hx253 : Bounds (30408539735743 / 1000000000000) (1909961980901 / 62500000000) x253 := by
    apply bounds_inv hx252 <;> norm_num
  let x254 : ℝ := x251*x253
  have hx254 : Bounds (49673681899 / 200000000000) (277011416883 / 1000000000000) x254 := by
    apply bounds_mul hx251 hx253 <;> norm_num
  let x255 : ℝ := x251/x252
  have hx255 : Bounds (49673681899 / 200000000000) (277011416883 / 1000000000000) x255 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx254
  let x256 : ℝ := (-2 / 1)*x255
  have hx256 : Bounds (-277011416883 / 500000000000) (-49673681899 / 100000000000) x256 := by
    apply bounds_mul (bounds_const ((-2 / 1) : ℝ)) hx255 <;> norm_num
  let x257 : ℝ := x256*x228
  have hx257 : Bounds (-792378836457 / 1000000000000) (-176785370493 / 250000000000) x257 := by
    apply bounds_mul hx256 hx228 <;> norm_num
  let x258 : ℝ := (2 / 1)*x182
  have hx258 : Bounds (1403926799 / 1000000000) (1404009249 / 1000000000) x258 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx182 <;> norm_num
  let x259 : ℝ := c*c
  have hx259 : Bounds (1092368601 / 62500000000) (175589001 / 10000000000) x259 := by
    apply bounds_mul hc hc <;> norm_num
  let x260 : ℝ := -x259
  have hx260 : Bounds (-175589001 / 10000000000) (-1092368601 / 62500000000) x260 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx259
  let x261 : ℝ := x258+x260
  have hx261 : Bounds (13863678989 / 10000000000) (173316418923 / 125000000000) x261 := by
    apply bounds_add hx258 hx260 <;> norm_num
  let x262 : ℝ := x258-x259
  have hx262 : Bounds (13863678989 / 10000000000) (173316418923 / 125000000000) x262 := by
    exact hx261
  let x263 : ℝ := c*x262
  have hx263 : Bounds (91641690853 / 500000000000) (45932317343 / 250000000000) x263 := by
    apply bounds_mul hc hx262 <;> norm_num
  let x264 : ℝ := x245*x245
  have hx264 : Bounds (475600149391 / 1000000000000) (47573445237 / 100000000000) x264 := by
    apply bounds_mul hx245 hx245 <;> norm_num
  let x265 : ℝ := x264⁻¹
  have hx265 : Bounds (210201299279 / 100000000000) (1051303286259 / 500000000000) x265 := by
    apply bounds_inv hx264 <;> norm_num
  let x266 : ℝ := x263*x265
  have hx266 : Bounds (96316012427 / 250000000000) (193155184673 / 500000000000) x266 := by
    apply bounds_mul hx263 hx265 <;> norm_num
  let x267 : ℝ := x263/x264
  have hx267 : Bounds (96316012427 / 250000000000) (193155184673 / 500000000000) x267 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx266
  let x268 : ℝ := (2 / 1)*x267
  have hx268 : Bounds (96316012427 / 125000000000) (193155184673 / 250000000000) x268 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx267 <;> norm_num
  let x269 : ℝ := x268*x235
  have hx269 : Bounds (199950088927 / 250000000000) (802384912859 / 1000000000000) x269 := by
    apply bounds_mul hx268 hx235 <;> norm_num
  let x270 : ℝ := x257+x269
  have hx270 : Bounds (7421519251 / 1000000000000) (95243430887 / 1000000000000) x270 := by
    apply bounds_add hx257 hx269 <;> norm_num
  have hPos : 0 < x270 :=
    lt_of_lt_of_le (by norm_num) hx270.1
  have hBridgeL : doubleCapBridgeL x = x48 := by
    exact hEll'
  rw [← doubleCapBridgeDerivativeTraceForm_eq x]
  simpa +zetaDelta only [doubleCapBridgeDerivativeTraceForm,
    hBridgeL, SmallMean.A, biasB, div_one, pow_two] using hPos

theorem acceptedCell : DoubleCapBridgeDerivativeCellCertificate
    (⟨19, by decide⟩ : Fin 256) doubleCapBridgeDerivativeExpression where
  positive x hx := by
    have hloEq : doubleCapBridgeLo (⟨19, by decide⟩ : Fin 256) =
        (1337 / 10240) := by norm_num [doubleCapBridgeLo, doubleCapBridgeStep]
    have hhiEq : doubleCapBridgeHi (⟨19, by decide⟩ : Fin 256) =
        (67 / 512) := by norm_num [doubleCapBridgeHi, doubleCapBridgeStep]
    have hlo : (1337 / 10240) ≤ x := by
      simpa only [hloEq] using hx.1
    have hhi : x ≤ (67 / 512) := by
      simpa only [hhiEq] using hx.2
    exact cell_derivative_pos x ⟨hlo, hhi⟩

#print axioms cell_derivative_pos
#print axioms acceptedCell

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell019

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell020 =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell020
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_derivative_pos (x : ℝ)
    (hx : Bounds (67 / 512) (1343 / 10240) x) :
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
  have hx0 : Bounds (67 / 256) (1343 / 5120) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx <;> norm_num
  let x1 : ℝ := Real.log (2 / 1)
  have hx1 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x1 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x2 : ℝ := Real.log (2 / 1)
  have hx2 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x2 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x3 : ℝ := (1 / 1)+(1343 / 5120)
  have hx3 : Bounds (6463 / 5120) (6463 / 5120) x3 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1343 / 5120) : ℝ)) <;> norm_num
  let x4 : ℝ := (1 / 1)+(1343 / 5120)
  have hx4 : Bounds (6463 / 5120) (6463 / 5120) x4 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1343 / 5120) : ℝ)) <;> norm_num
  let x5 : ℝ := Real.log x4
  have hx5 : Bounds (232939167 / 1000000000) (7279349 / 31250000) x5 := by
    exact bounds_log hx4 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x6 : ℝ := x3*x5
  have hx6 : Bounds (147020101203 / 500000000000) (294040203669 / 1000000000000) x6 := by
    apply bounds_mul hx3 hx5 <;> norm_num
  let x7 : ℝ := -(1343 / 5120)
  have hx7 : Bounds (-1343 / 5120) (-1343 / 5120) x7 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1343 / 5120) : ℝ))
  let x8 : ℝ := (1 / 1)+x7
  have hx8 : Bounds (3777 / 5120) (3777 / 5120) x8 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx7 <;> norm_num
  let x9 : ℝ := (1 / 1)-(1343 / 5120)
  have hx9 : Bounds (3777 / 5120) (3777 / 5120) x9 := by
    exact hx8
  let x10 : ℝ := -(1343 / 5120)
  have hx10 : Bounds (-1343 / 5120) (-1343 / 5120) x10 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1343 / 5120) : ℝ))
  let x11 : ℝ := (1 / 1)+x10
  have hx11 : Bounds (3777 / 5120) (3777 / 5120) x11 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx10 <;> norm_num
  let x12 : ℝ := (1 / 1)-(1343 / 5120)
  have hx12 : Bounds (3777 / 5120) (3777 / 5120) x12 := by
    exact hx11
  let x13 : ℝ := Real.log x12
  have hx13 : Bounds (-76056099 / 250000000) (-60844879 / 200000000) x13 := by
    exact bounds_log hx12 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x14 : ℝ := x9*x13
  have hx14 : Bounds (-112212455439 / 500000000000) (-224424910139 / 1000000000000) x14 := by
    apply bounds_mul hx9 hx13 <;> norm_num
  let x15 : ℝ := x6+x14
  have hx15 : Bounds (8701911441 / 125000000000) (6961529353 / 100000000000) x15 := by
    apply bounds_add hx6 hx14 <;> norm_num
  let x16 : ℝ := (2 / 1)⁻¹
  have hx16 : Bounds (1 / 2) (1 / 2) x16 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x17 : ℝ := x15*x16
  have hx17 : Bounds (8701911441 / 250000000000) (6961529353 / 200000000000) x17 := by
    apply bounds_mul hx15 hx16 <;> norm_num
  let x18 : ℝ := x15/(2 / 1)
  have hx18 : Bounds (8701911441 / 250000000000) (6961529353 / 200000000000) x18 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx17
  let x19 : ℝ := -x18
  have hx19 : Bounds (-6961529353 / 200000000000) (-8701911441 / 250000000000) x19 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx18
  let x20 : ℝ := x2+x19
  have hx20 : Bounds (131667906647 / 200000000000) (164584883809 / 250000000000) x20 := by
    apply bounds_add hx2 hx19 <;> norm_num
  let x21 : ℝ := x2-x18
  have hx21 : Bounds (131667906647 / 200000000000) (164584883809 / 250000000000) x21 := by
    exact hx20
  let x22 : ℝ := biasE (1343 / 5120)
  have hx22 : Bounds (131667906647 / 200000000000) (164584883809 / 250000000000) x22 := by
    simpa +zetaDelta only [biasE, div_one] using hx21
  let x23 : ℝ := Real.log (2 / 1)
  have hx23 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x23 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x24 : ℝ := (1 / 1)+(67 / 256)
  have hx24 : Bounds (323 / 256) (323 / 256) x24 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((67 / 256) : ℝ)) <;> norm_num
  let x25 : ℝ := (1 / 1)+(67 / 256)
  have hx25 : Bounds (323 / 256) (323 / 256) x25 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((67 / 256) : ℝ)) <;> norm_num
  let x26 : ℝ := Real.log x25
  have hx26 : Bounds (116237439 / 500000000) (232474879 / 1000000000) x26 := by
    exact bounds_log hx25 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x27 : ℝ := x24*x26
  have hx27 : Bounds (73329478119 / 250000000000) (293317913739 / 1000000000000) x27 := by
    apply bounds_mul hx24 hx26 <;> norm_num
  let x28 : ℝ := -(67 / 256)
  have hx28 : Bounds (-67 / 256) (-67 / 256) x28 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((67 / 256) : ℝ))
  let x29 : ℝ := (1 / 1)+x28
  have hx29 : Bounds (189 / 256) (189 / 256) x29 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx28 <;> norm_num
  let x30 : ℝ := (1 / 1)-(67 / 256)
  have hx30 : Bounds (189 / 256) (189 / 256) x30 := by
    exact hx29
  let x31 : ℝ := -(67 / 256)
  have hx31 : Bounds (-67 / 256) (-67 / 256) x31 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((67 / 256) : ℝ))
  let x32 : ℝ := (1 / 1)+x31
  have hx32 : Bounds (189 / 256) (189 / 256) x32 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx31 <;> norm_num
  let x33 : ℝ := (1 / 1)-(67 / 256)
  have hx33 : Bounds (189 / 256) (189 / 256) x33 := by
    exact hx32
  let x34 : ℝ := Real.log x33
  have hx34 : Bounds (-30343043 / 100000000) (-303430429 / 1000000000) x34 := by
    exact bounds_log hx33 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x35 : ℝ := x30*x34
  have hx35 : Bounds (-224016997149 / 1000000000000) (-22401699641 / 100000000000) x35 := by
    apply bounds_mul hx30 hx34 <;> norm_num
  let x36 : ℝ := x27+x35
  have hx36 : Bounds (69300915327 / 1000000000000) (69300917329 / 1000000000000) x36 := by
    apply bounds_add hx27 hx35 <;> norm_num
  let x37 : ℝ := (2 / 1)⁻¹
  have hx37 : Bounds (1 / 2) (1 / 2) x37 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x38 : ℝ := x36*x37
  have hx38 : Bounds (34650457663 / 1000000000000) (6930091733 / 200000000000) x38 := by
    apply bounds_mul hx36 hx37 <;> norm_num
  let x39 : ℝ := x36/(2 / 1)
  have hx39 : Bounds (34650457663 / 1000000000000) (6930091733 / 200000000000) x39 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx38
  let x40 : ℝ := -x39
  have hx40 : Bounds (-6930091733 / 200000000000) (-34650457663 / 1000000000000) x40 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx39
  let x41 : ℝ := x23+x40
  have hx41 : Bounds (131699344267 / 200000000000) (658496723337 / 1000000000000) x41 := by
    apply bounds_add hx23 hx40 <;> norm_num
  let x42 : ℝ := x23-x39
  have hx42 : Bounds (131699344267 / 200000000000) (658496723337 / 1000000000000) x42 := by
    exact hx41
  let x43 : ℝ := biasE (67 / 256)
  have hx43 : Bounds (131699344267 / 200000000000) (658496723337 / 1000000000000) x43 := by
    simpa +zetaDelta only [biasE, div_one] using hx42
  let x44 : ℝ := biasE x0
  have hx44 : Bounds (131667906647 / 200000000000) (658496723337 / 1000000000000) x44 := by
    exact bounds_biasE hx0 (by norm_num) (by norm_num) hx22.1 hx43.2
  let x45 : ℝ := x1+x44
  have hx45 : Bounds (270297342647 / 200000000000) (1351643904337 / 1000000000000) x45 := by
    apply bounds_add hx1 hx44 <;> norm_num
  let x46 : ℝ := (2 / 1)⁻¹
  have hx46 : Bounds (1 / 2) (1 / 2) x46 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x47 : ℝ := x45*x46
  have hx47 : Bounds (675743356617 / 1000000000000) (675821952169 / 1000000000000) x47 := by
    apply bounds_mul hx45 hx46 <;> norm_num
  let x48 : ℝ := x45/(2 / 1)
  have hx48 : Bounds (675743356617 / 1000000000000) (675821952169 / 1000000000000) x48 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx47
  let x49 : ℝ := Real.log (2 / 1)
  have hx49 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x49 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x50 : ℝ := (1 / 1)+(92803 / 500000)
  have hx50 : Bounds (592803 / 500000) (592803 / 500000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((92803 / 500000) : ℝ)) <;> norm_num
  let x51 : ℝ := (1 / 1)+(92803 / 500000)
  have hx51 : Bounds (592803 / 500000) (592803 / 500000) x51 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((92803 / 500000) : ℝ)) <;> norm_num
  let x52 : ℝ := Real.log x51
  have hx52 : Bounds (42563509 / 250000000) (170254037 / 1000000000) x52 := by
    exact bounds_log hx51 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x53 : ℝ := x50*x52
  have hx53 : Bounds (40370841321 / 200000000000) (12615887987 / 62500000000) x53 := by
    apply bounds_mul hx50 hx52 <;> norm_num
  let x54 : ℝ := -(92803 / 500000)
  have hx54 : Bounds (-92803 / 500000) (-92803 / 500000) x54 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((92803 / 500000) : ℝ))
  let x55 : ℝ := (1 / 1)+x54
  have hx55 : Bounds (407197 / 500000) (407197 / 500000) x55 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx54 <;> norm_num
  let x56 : ℝ := (1 / 1)-(92803 / 500000)
  have hx56 : Bounds (407197 / 500000) (407197 / 500000) x56 := by
    exact hx55
  let x57 : ℝ := -(92803 / 500000)
  have hx57 : Bounds (-92803 / 500000) (-92803 / 500000) x57 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((92803 / 500000) : ℝ))
  let x58 : ℝ := (1 / 1)+x57
  have hx58 : Bounds (407197 / 500000) (407197 / 500000) x58 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx57 <;> norm_num
  let x59 : ℝ := (1 / 1)-(92803 / 500000)
  have hx59 : Bounds (407197 / 500000) (407197 / 500000) x59 := by
    exact hx58
  let x60 : ℝ := Real.log x59
  have hx60 : Bounds (-205311001 / 1000000000) (-205311 / 1000000) x60 := by
    exact bounds_log hx59 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x61 : ℝ := x56*x60
  have hx61 : Bounds (-167204047349 / 1000000000000) (-83602023267 / 500000000000) x61 := by
    apply bounds_mul hx56 hx60 <;> norm_num
  let x62 : ℝ := x53+x61
  have hx62 : Bounds (4331269907 / 125000000000) (17325080629 / 500000000000) x62 := by
    apply bounds_add hx53 hx61 <;> norm_num
  let x63 : ℝ := (2 / 1)⁻¹
  have hx63 : Bounds (1 / 2) (1 / 2) x63 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x64 : ℝ := x62*x63
  have hx64 : Bounds (4331269907 / 250000000000) (17325080629 / 1000000000000) x64 := by
    apply bounds_mul hx62 hx63 <;> norm_num
  let x65 : ℝ := x62/(2 / 1)
  have hx65 : Bounds (4331269907 / 250000000000) (17325080629 / 1000000000000) x65 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx64
  let x66 : ℝ := -x65
  have hx66 : Bounds (-17325080629 / 1000000000000) (-4331269907 / 250000000000) x66 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx65
  let x67 : ℝ := x49+x66
  have hx67 : Bounds (675822099371 / 1000000000000) (168955525343 / 250000000000) x67 := by
    apply bounds_add hx49 hx66 <;> norm_num
  let x68 : ℝ := x49-x65
  have hx68 : Bounds (675822099371 / 1000000000000) (168955525343 / 250000000000) x68 := by
    exact hx67
  let x69 : ℝ := biasE (92803 / 500000)
  have hx69 : Bounds (675822099371 / 1000000000000) (168955525343 / 250000000000) x69 := by
    simpa +zetaDelta only [biasE, div_one] using hx68
  let x70 : ℝ := Real.log (2 / 1)
  have hx70 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x70 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x71 : ℝ := (1 / 1)+(7441 / 40000)
  have hx71 : Bounds (47441 / 40000) (47441 / 40000) x71 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((7441 / 40000) : ℝ)) <;> norm_num
  let x72 : ℝ := (1 / 1)+(7441 / 40000)
  have hx72 : Bounds (47441 / 40000) (47441 / 40000) x72 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((7441 / 40000) : ℝ)) <;> norm_num
  let x73 : ℝ := Real.log x72
  have hx73 : Bounds (170607379 / 1000000000) (8530369 / 50000000) x73 := by
    exact bounds_log hx72 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x74 : ℝ := x71*x73
  have hx74 : Bounds (101172308339 / 500000000000) (40468923573 / 200000000000) x74 := by
    apply bounds_mul hx71 hx73 <;> norm_num
  let x75 : ℝ := -(7441 / 40000)
  have hx75 : Bounds (-7441 / 40000) (-7441 / 40000) x75 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((7441 / 40000) : ℝ))
  let x76 : ℝ := (1 / 1)+x75
  have hx76 : Bounds (32559 / 40000) (32559 / 40000) x76 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx75 <;> norm_num
  let x77 : ℝ := (1 / 1)-(7441 / 40000)
  have hx77 : Bounds (32559 / 40000) (32559 / 40000) x77 := by
    exact hx76
  let x78 : ℝ := -(7441 / 40000)
  have hx78 : Bounds (-7441 / 40000) (-7441 / 40000) x78 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((7441 / 40000) : ℝ))
  let x79 : ℝ := (1 / 1)+x78
  have hx79 : Bounds (32559 / 40000) (32559 / 40000) x79 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx78 <;> norm_num
  let x80 : ℝ := (1 / 1)-(7441 / 40000)
  have hx80 : Bounds (32559 / 40000) (32559 / 40000) x80 := by
    exact hx79
  let x81 : ℝ := Real.log x80
  have hx81 : Bounds (-102912813 / 500000000) (-329321 / 1600000) x81 := by
    exact bounds_log hx80 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x82 : ℝ := x77*x81
  have hx82 : Bounds (-41884228481 / 250000000000) (-167536913109 / 1000000000000) x82 := by
    apply bounds_mul hx77 hx81 <;> norm_num
  let x83 : ℝ := x74+x82
  have hx83 : Bounds (17403851377 / 500000000000) (8701926189 / 250000000000) x83 := by
    apply bounds_add hx74 hx82 <;> norm_num
  let x84 : ℝ := (2 / 1)⁻¹
  have hx84 : Bounds (1 / 2) (1 / 2) x84 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x85 : ℝ := x83*x84
  have hx85 : Bounds (17403851377 / 1000000000000) (8701926189 / 500000000000) x85 := by
    apply bounds_mul hx83 hx84 <;> norm_num
  let x86 : ℝ := x83/(2 / 1)
  have hx86 : Bounds (17403851377 / 1000000000000) (8701926189 / 500000000000) x86 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx85
  let x87 : ℝ := -x86
  have hx87 : Bounds (-8701926189 / 500000000000) (-17403851377 / 1000000000000) x87 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx86
  let x88 : ℝ := x70+x87
  have hx88 : Bounds (337871663811 / 500000000000) (675743329623 / 1000000000000) x88 := by
    apply bounds_add hx70 hx87 <;> norm_num
  let x89 : ℝ := x70-x86
  have hx89 : Bounds (337871663811 / 500000000000) (675743329623 / 1000000000000) x89 := by
    exact hx88
  let x90 : ℝ := biasE (7441 / 40000)
  have hx90 : Bounds (337871663811 / 500000000000) (675743329623 / 1000000000000) x90 := by
    simpa +zetaDelta only [biasE, div_one] using hx89
  let y : ℝ := doubleCapHighTailY x
  have hEll' : Real.log 2 * doubleCapHighTailFloor x = x48 := by
    simpa +zetaDelta only [div_one] using hEll
  have hy : Bounds (92803 / 500000) (7441 / 40000) y := by
    dsimp only [y, doubleCapHighTailY]
    apply entropyInverseBias_bracket hh0.le hh1.le
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (7441 / 40000) ≤ (675743329623 / 1000000000000) := hx90.2
      have h2 : (675743356617 / 1000000000000) ≤ x48 := hx48.1
      linarith [hEll']
    · have h1 : x48 ≤ (675821952169 / 1000000000000) := hx48.2
      have h2 : (675822099371 / 1000000000000) ≤ biasE (92803 / 500000) := hx69.1
      linarith [hEll']
  let x91 : ℝ := x⁻¹
  have hx91 : Bounds (1524944154877 / 200000000000) (7641791044777 / 1000000000000) x91 := by
    apply bounds_inv hx <;> norm_num
  let x92 : ℝ := x48*x91
  have hx92 : Bounds (103047088187 / 20000000000) (5164490141949 / 1000000000000) x92 := by
    apply bounds_mul hx48 hx91 <;> norm_num
  let x93 : ℝ := x48/x
  have hx93 : Bounds (103047088187 / 20000000000) (5164490141949 / 1000000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(132509 / 1000000)
  have hx95 : Bounds (1132509 / 1000000) (1132509 / 1000000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((132509 / 1000000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(132509 / 1000000)
  have hx96 : Bounds (1132509 / 1000000) (1132509 / 1000000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((132509 / 1000000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (4977421 / 40000000) (62217763 / 500000000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (70462175991 / 500000000000) (28184870623 / 200000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(132509 / 1000000)
  have hx99 : Bounds (-132509 / 1000000) (-132509 / 1000000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((132509 / 1000000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (867491 / 1000000) (867491 / 1000000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(132509 / 1000000)
  have hx101 : Bounds (867491 / 1000000) (867491 / 1000000) x101 := by
    exact hx100
  let x102 : ℝ := -(132509 / 1000000)
  have hx102 : Bounds (-132509 / 1000000) (-132509 / 1000000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((132509 / 1000000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (867491 / 1000000) (867491 / 1000000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(132509 / 1000000)
  have hx104 : Bounds (867491 / 1000000) (867491 / 1000000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-71075071 / 500000000) (-142150141 / 1000000000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-61656984417 / 500000000000) (-61656983983 / 500000000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (4402595787 / 250000000000) (17610385149 / 1000000000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (4402595787 / 500000000000) (352207703 / 40000000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (4402595787 / 500000000000) (352207703 / 40000000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-352207703 / 40000000000) (-4402595787 / 500000000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (27373679497 / 40000000000) (342170994713 / 500000000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (27373679497 / 40000000000) (342170994713 / 500000000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (132509 / 1000000)
  have hx114 : Bounds (27373679497 / 40000000000) (342170994713 / 500000000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(66407 / 500000)
  have hx116 : Bounds (566407 / 500000) (566407 / 500000) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((66407 / 500000) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(66407 / 500000)
  have hx117 : Bounds (566407 / 500000) (566407 / 500000) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((66407 / 500000) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (62352401 / 500000000) (124704803 / 1000000000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (35316836393 / 250000000000) (70633673353 / 500000000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(66407 / 500000)
  have hx120 : Bounds (-66407 / 500000) (-66407 / 500000) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((66407 / 500000) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (433593 / 500000) (433593 / 500000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(66407 / 500000)
  have hx122 : Bounds (433593 / 500000) (433593 / 500000) x122 := by
    exact hx121
  let x123 : ℝ := -(66407 / 500000)
  have hx123 : Bounds (-66407 / 500000) (-66407 / 500000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((66407 / 500000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (433593 / 500000) (433593 / 500000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(66407 / 500000)
  have hx125 : Bounds (433593 / 500000) (433593 / 500000) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-142501793 / 1000000000) (-4453181 / 31250000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-24715111973 / 200000000000) (-123575558997 / 1000000000000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (17691785707 / 1000000000000) (17691787709 / 1000000000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (8845892853 / 1000000000000) (1769178771 / 200000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (8845892853 / 1000000000000) (1769178771 / 200000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-1769178771 / 200000000000) (-8845892853 / 1000000000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (136860257229 / 200000000000) (684301288147 / 1000000000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (136860257229 / 200000000000) (684301288147 / 1000000000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (66407 / 500000)
  have hx135 : Bounds (136860257229 / 200000000000) (684301288147 / 1000000000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(132509 / 1000000)
  have hx136 : Bounds (170683332607 / 250000000000) (34217071211 / 50000000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((132509 / 1000000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(66407 / 500000)
  have hx137 : Bounds (684304798523 / 1000000000000) (685916593713 / 1000000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((66407 / 500000) : ℝ)) <;> norm_num
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
  have hc : Bounds (132509 / 1000000) (66407 / 500000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num)
      (by norm_num) (show 0 < x93 by linarith [hx93.1]) hcEq
    · have h1 : x93 * (132509 / 1000000) ≤ (34217071211 / 50000000000) := hx136.2
      have h2 : (27373679497 / 40000000000) ≤ biasE (132509 / 1000000) := hx114.1
      linarith
    · have h1 : biasE (66407 / 500000) ≤ (684301288147 / 1000000000000) := hx135.2
      have h2 : (684304798523 / 1000000000000) ≤ x93 * (66407 / 500000) := hx137.1
      linarith
  let x138 : ℝ := (1 / 1)+x0
  have hx138 : Bounds (323 / 256) (6463 / 5120) x138 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx0 <;> norm_num
  let x139 : ℝ := -x0
  have hx139 : Bounds (-1343 / 5120) (-67 / 256) x139 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x140 : ℝ := (1 / 1)+x139
  have hx140 : Bounds (3777 / 5120) (189 / 256) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx139 <;> norm_num
  let x141 : ℝ := (1 / 1)-x0
  have hx141 : Bounds (3777 / 5120) (189 / 256) x141 := by
    exact hx140
  let x142 : ℝ := x141⁻¹
  have hx142 : Bounds (1354497354497 / 1000000000000) (1355573206249 / 1000000000000) x142 := by
    apply bounds_inv hx141 <;> norm_num
  let x143 : ℝ := x138*x142
  have hx143 : Bounds (854497354497 / 500000000000) (855573206249 / 500000000000) x143 := by
    apply bounds_mul hx138 hx142 <;> norm_num
  let x144 : ℝ := x138/x141
  have hx144 : Bounds (854497354497 / 500000000000) (855573206249 / 500000000000) x144 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx143
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (133976327 / 250000000) (537163563 / 1000000000) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_14.2)
  let x146 : ℝ := (2 / 1)⁻¹
  have hx146 : Bounds (1 / 2) (1 / 2) x146 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x147 : ℝ := x145*x146
  have hx147 : Bounds (133976327 / 500000000) (537163563 / 2000000000) x147 := by
    apply bounds_mul hx145 hx146 <;> norm_num
  let x148 : ℝ := x145/(2 / 1)
  have hx148 : Bounds (133976327 / 500000000) (537163563 / 2000000000) x148 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx147
  let x149 : ℝ := (1 / 1)+y
  have hx149 : Bounds (592803 / 500000) (47441 / 40000) x149 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x150 : ℝ := -y
  have hx150 : Bounds (-7441 / 40000) (-92803 / 500000) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (32559 / 40000) (407197 / 500000) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-y
  have hx152 : Bounds (32559 / 40000) (407197 / 500000) x152 := by
    exact hx151
  let x153 : ℝ := x152⁻¹
  have hx153 : Bounds (245581377073 / 200000000000) (614269480021 / 500000000000) x153 := by
    apply bounds_inv hx152 <;> norm_num
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (145581377073 / 100000000000) (364269480021 / 250000000000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x149/x152
  have hx155 : Bounds (145581377073 / 100000000000) (364269480021 / 250000000000) x155 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx154
  let x156 : ℝ := Real.log x155
  have hx156 : Bounds (93891259 / 250000000) (188216503 / 500000000) x156 := by
    exact bounds_log hx155 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_16.2)
  let x157 : ℝ := (2 / 1)⁻¹
  have hx157 : Bounds (1 / 2) (1 / 2) x157 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x158 : ℝ := x156*x157
  have hx158 : Bounds (93891259 / 500000000) (188216503 / 1000000000) x158 := by
    apply bounds_mul hx156 hx157 <;> norm_num
  let x159 : ℝ := x156/(2 / 1)
  have hx159 : Bounds (93891259 / 500000000) (188216503 / 1000000000) x159 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx158
  let x160 : ℝ := (1 / 1)+c
  have hx160 : Bounds (1132509 / 1000000) (566407 / 500000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x161 : ℝ := -c
  have hx161 : Bounds (-66407 / 500000) (-132509 / 1000000) x161 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x162 : ℝ := (1 / 1)+x161
  have hx162 : Bounds (433593 / 500000) (867491 / 1000000) x162 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx161 <;> norm_num
  let x163 : ℝ := (1 / 1)-c
  have hx163 : Bounds (433593 / 500000) (867491 / 1000000) x163 := by
    exact hx162
  let x164 : ℝ := x163⁻¹
  have hx164 : Bounds (288187427881 / 250000000000) (5765775739 / 5000000000) x164 := by
    apply bounds_inv hx163 <;> norm_num
  let x165 : ℝ := x160*x164
  have hx165 : Bounds (163187427881 / 125000000000) (3265775739 / 2500000000) x165 := by
    apply bounds_mul hx160 hx164 <;> norm_num
  let x166 : ℝ := x160/x163
  have hx166 : Bounds (163187427881 / 125000000000) (3265775739 / 2500000000) x166 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx165
  let x167 : ℝ := Real.log x166
  have hx167 : Bounds (266585667 / 1000000000) (53441319 / 200000000) x167 := by
    exact bounds_log hx166 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x168 : ℝ := (2 / 1)⁻¹
  have hx168 : Bounds (1 / 2) (1 / 2) x168 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x169 : ℝ := x167*x168
  have hx169 : Bounds (266585667 / 2000000000) (53441319 / 400000000) x169 := by
    apply bounds_mul hx167 hx168 <;> norm_num
  let x170 : ℝ := x167/(2 / 1)
  have hx170 : Bounds (266585667 / 2000000000) (53441319 / 400000000) x170 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx169
  let x171 : ℝ := Real.log (2 / 1)
  have hx171 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x171 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x172 : ℝ := c*c
  have hx172 : Bounds (17558635081 / 1000000000000) (4409889649 / 250000000000) x172 := by
    apply bounds_mul hc hc <;> norm_num
  let x173 : ℝ := -x172
  have hx173 : Bounds (-4409889649 / 250000000000) (-17558635081 / 1000000000000) x173 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx172
  let x174 : ℝ := (1 / 1)+x173
  have hx174 : Bounds (245590110351 / 250000000000) (982441364919 / 1000000000000) x174 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx173 <;> norm_num
  let x175 : ℝ := (1 / 1)-x172
  have hx175 : Bounds (245590110351 / 250000000000) (982441364919 / 1000000000000) x175 := by
    exact hx174
  let x176 : ℝ := Real.log x175
  have hx176 : Bounds (-1779699 / 100000000) (-2214327 / 125000000) x176 := by
    exact bounds_log hx175 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (-1779699 / 200000000) (-2214327 / 250000000) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (-1779699 / 200000000) (-2214327 / 250000000) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (2214327 / 250000000) (1779699 / 200000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x171+x180
  have hx181 : Bounds (87750561 / 125000000) (175511419 / 250000000) x181 := by
    apply bounds_add hx171 hx180 <;> norm_num
  let x182 : ℝ := x171-x179
  have hx182 : Bounds (87750561 / 125000000) (175511419 / 250000000) x182 := by
    exact hx181
  let x183 : ℝ := Real.log (2 / 1)
  have hx183 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x183 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x184 : ℝ := (1 / 1)+(66407 / 500000)
  have hx184 : Bounds (566407 / 500000) (566407 / 500000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((66407 / 500000) : ℝ)) <;> norm_num
  let x185 : ℝ := (1 / 1)+(66407 / 500000)
  have hx185 : Bounds (566407 / 500000) (566407 / 500000) x185 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((66407 / 500000) : ℝ)) <;> norm_num
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (62352401 / 500000000) (124704803 / 1000000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x187 : ℝ := x184*x186
  have hx187 : Bounds (35316836393 / 250000000000) (70633673353 / 500000000000) x187 := by
    apply bounds_mul hx184 hx186 <;> norm_num
  let x188 : ℝ := -(66407 / 500000)
  have hx188 : Bounds (-66407 / 500000) (-66407 / 500000) x188 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((66407 / 500000) : ℝ))
  let x189 : ℝ := (1 / 1)+x188
  have hx189 : Bounds (433593 / 500000) (433593 / 500000) x189 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx188 <;> norm_num
  let x190 : ℝ := (1 / 1)-(66407 / 500000)
  have hx190 : Bounds (433593 / 500000) (433593 / 500000) x190 := by
    exact hx189
  let x191 : ℝ := -(66407 / 500000)
  have hx191 : Bounds (-66407 / 500000) (-66407 / 500000) x191 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((66407 / 500000) : ℝ))
  let x192 : ℝ := (1 / 1)+x191
  have hx192 : Bounds (433593 / 500000) (433593 / 500000) x192 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx191 <;> norm_num
  let x193 : ℝ := (1 / 1)-(66407 / 500000)
  have hx193 : Bounds (433593 / 500000) (433593 / 500000) x193 := by
    exact hx192
  let x194 : ℝ := Real.log x193
  have hx194 : Bounds (-142501793 / 1000000000) (-4453181 / 31250000) x194 := by
    exact bounds_log hx193 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x195 : ℝ := x190*x194
  have hx195 : Bounds (-24715111973 / 200000000000) (-123575558997 / 1000000000000) x195 := by
    apply bounds_mul hx190 hx194 <;> norm_num
  let x196 : ℝ := x187+x195
  have hx196 : Bounds (17691785707 / 1000000000000) (17691787709 / 1000000000000) x196 := by
    apply bounds_add hx187 hx195 <;> norm_num
  let x197 : ℝ := (2 / 1)⁻¹
  have hx197 : Bounds (1 / 2) (1 / 2) x197 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x198 : ℝ := x196*x197
  have hx198 : Bounds (8845892853 / 1000000000000) (1769178771 / 200000000000) x198 := by
    apply bounds_mul hx196 hx197 <;> norm_num
  let x199 : ℝ := x196/(2 / 1)
  have hx199 : Bounds (8845892853 / 1000000000000) (1769178771 / 200000000000) x199 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx198
  let x200 : ℝ := -x199
  have hx200 : Bounds (-1769178771 / 200000000000) (-8845892853 / 1000000000000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx199
  let x201 : ℝ := x183+x200
  have hx201 : Bounds (136860257229 / 200000000000) (684301288147 / 1000000000000) x201 := by
    apply bounds_add hx183 hx200 <;> norm_num
  let x202 : ℝ := x183-x199
  have hx202 : Bounds (136860257229 / 200000000000) (684301288147 / 1000000000000) x202 := by
    exact hx201
  let x203 : ℝ := biasE (66407 / 500000)
  have hx203 : Bounds (136860257229 / 200000000000) (684301288147 / 1000000000000) x203 := by
    simpa +zetaDelta only [biasE, div_one] using hx202
  let x204 : ℝ := Real.log (2 / 1)
  have hx204 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x204 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x205 : ℝ := (1 / 1)+(132509 / 1000000)
  have hx205 : Bounds (1132509 / 1000000) (1132509 / 1000000) x205 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((132509 / 1000000) : ℝ)) <;> norm_num
  let x206 : ℝ := (1 / 1)+(132509 / 1000000)
  have hx206 : Bounds (1132509 / 1000000) (1132509 / 1000000) x206 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((132509 / 1000000) : ℝ)) <;> norm_num
  let x207 : ℝ := Real.log x206
  have hx207 : Bounds (4977421 / 40000000) (62217763 / 500000000) x207 := by
    exact bounds_log hx206 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x208 : ℝ := x205*x207
  have hx208 : Bounds (70462175991 / 500000000000) (28184870623 / 200000000000) x208 := by
    apply bounds_mul hx205 hx207 <;> norm_num
  let x209 : ℝ := -(132509 / 1000000)
  have hx209 : Bounds (-132509 / 1000000) (-132509 / 1000000) x209 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((132509 / 1000000) : ℝ))
  let x210 : ℝ := (1 / 1)+x209
  have hx210 : Bounds (867491 / 1000000) (867491 / 1000000) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx209 <;> norm_num
  let x211 : ℝ := (1 / 1)-(132509 / 1000000)
  have hx211 : Bounds (867491 / 1000000) (867491 / 1000000) x211 := by
    exact hx210
  let x212 : ℝ := -(132509 / 1000000)
  have hx212 : Bounds (-132509 / 1000000) (-132509 / 1000000) x212 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((132509 / 1000000) : ℝ))
  let x213 : ℝ := (1 / 1)+x212
  have hx213 : Bounds (867491 / 1000000) (867491 / 1000000) x213 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx212 <;> norm_num
  let x214 : ℝ := (1 / 1)-(132509 / 1000000)
  have hx214 : Bounds (867491 / 1000000) (867491 / 1000000) x214 := by
    exact hx213
  let x215 : ℝ := Real.log x214
  have hx215 : Bounds (-71075071 / 500000000) (-142150141 / 1000000000) x215 := by
    exact bounds_log hx214 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x216 : ℝ := x211*x215
  have hx216 : Bounds (-61656984417 / 500000000000) (-61656983983 / 500000000000) x216 := by
    apply bounds_mul hx211 hx215 <;> norm_num
  let x217 : ℝ := x208+x216
  have hx217 : Bounds (4402595787 / 250000000000) (17610385149 / 1000000000000) x217 := by
    apply bounds_add hx208 hx216 <;> norm_num
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (4402595787 / 500000000000) (352207703 / 40000000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (4402595787 / 500000000000) (352207703 / 40000000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := -x220
  have hx221 : Bounds (-352207703 / 40000000000) (-4402595787 / 500000000000) x221 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx220
  let x222 : ℝ := x204+x221
  have hx222 : Bounds (27373679497 / 40000000000) (342170994713 / 500000000000) x222 := by
    apply bounds_add hx204 hx221 <;> norm_num
  let x223 : ℝ := x204-x220
  have hx223 : Bounds (27373679497 / 40000000000) (342170994713 / 500000000000) x223 := by
    exact hx222
  let x224 : ℝ := biasE (132509 / 1000000)
  have hx224 : Bounds (27373679497 / 40000000000) (342170994713 / 500000000000) x224 := by
    simpa +zetaDelta only [biasE, div_one] using hx223
  let x225 : ℝ := biasE c
  have hx225 : Bounds (136860257229 / 200000000000) (342170994713 / 500000000000) x225 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx203.1 hx224.2
  let x226 : ℝ := x159⁻¹
  have hx226 : Bounds (5313030388201 / 1000000000000) (665663669501 / 125000000000) x226 := by
    apply bounds_inv hx159 <;> norm_num
  let x227 : ℝ := x148*x226
  have hx227 : Bounds (1423640593301 / 1000000000000) (357570268469 / 250000000000) x227 := by
    apply bounds_mul hx148 hx226 <;> norm_num
  let x228 : ℝ := x148/x159
  have hx228 : Bounds (1423640593301 / 1000000000000) (357570268469 / 250000000000) x228 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx227
  let x229 : ℝ := c*x148
  have hx229 : Bounds (8876534557 / 250000000000) (35671420729 / 1000000000000) x229 := by
    apply bounds_mul hc hx148 <;> norm_num
  let x230 : ℝ := x225+x229
  have hx230 : Bounds (719807424373 / 1000000000000) (144002682031 / 200000000000) x230 := by
    apply bounds_add hx225 hx229 <;> norm_num
  let x231 : ℝ := x*x170
  have hx231 : Bounds (17442616883 / 1000000000000) (10951491 / 625000000) x231 := by
    apply bounds_mul hx hx170 <;> norm_num
  let x232 : ℝ := x48+x231
  have hx232 : Bounds (1386371947 / 2000000000) (693344337769 / 1000000000000) x232 := by
    apply bounds_add hx48 hx231 <;> norm_num
  let x233 : ℝ := x232⁻¹
  have hx233 : Bounds (1442284800677 / 1000000000000) (721307151493 / 500000000000) x233 := by
    apply bounds_inv hx232 <;> norm_num
  let x234 : ℝ := x230*x233
  have hx234 : Bounds (1038167307587 / 1000000000000) (129837705479 / 125000000000) x234 := by
    apply bounds_mul hx230 hx233 <;> norm_num
  let x235 : ℝ := x230/x232
  have hx235 : Bounds (1038167307587 / 1000000000000) (129837705479 / 125000000000) x235 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx234
  let x236 : ℝ := y*y
  have hx236 : Bounds (8612396809 / 250000000000) (55368481 / 1600000000) x236 := by
    apply bounds_mul hy hy <;> norm_num
  let x237 : ℝ := -x236
  have hx237 : Bounds (-55368481 / 1600000000) (-8612396809 / 250000000000) x237 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx236
  let x238 : ℝ := (1 / 1)+x237
  have hx238 : Bounds (1544631519 / 1600000000) (241387603191 / 250000000000) x238 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx237 <;> norm_num
  let x239 : ℝ := (1 / 1)-x236
  have hx239 : Bounds (1544631519 / 1600000000) (241387603191 / 250000000000) x239 := by
    exact hx238
  let x240 : ℝ := x239*x159
  have hx240 : Bounds (22660530939 / 125000000000) (181732522161 / 1000000000000) x240 := by
    apply bounds_mul hx239 hx159 <;> norm_num
  let x241 : ℝ := c*c
  have hx241 : Bounds (17558635081 / 1000000000000) (4409889649 / 250000000000) x241 := by
    apply bounds_mul hc hc <;> norm_num
  let x242 : ℝ := -x241
  have hx242 : Bounds (-4409889649 / 250000000000) (-17558635081 / 1000000000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx241
  let x243 : ℝ := (1 / 1)+x242
  have hx243 : Bounds (245590110351 / 250000000000) (982441364919 / 1000000000000) x243 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx242 <;> norm_num
  let x244 : ℝ := (1 / 1)-x241
  have hx244 : Bounds (245590110351 / 250000000000) (982441364919 / 1000000000000) x244 := by
    exact hx243
  let x245 : ℝ := x244*x182
  have hx245 : Bounds (689621438699 / 1000000000000) (137943742433 / 200000000000) x245 := by
    apply bounds_mul hx244 hx182 <;> norm_num
  let x246 : ℝ := y*y
  have hx246 : Bounds (8612396809 / 250000000000) (55368481 / 1600000000) x246 := by
    apply bounds_mul hy hy <;> norm_num
  let x247 : ℝ := (1 / 1)+x246
  have hx247 : Bounds (258612396809 / 250000000000) (1655368481 / 1600000000) x247 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx246 <;> norm_num
  let x248 : ℝ := x247*x159
  have hx248 : Bounds (38850309647 / 200000000000) (194729791669 / 1000000000000) x248 := by
    apply bounds_mul hx247 hx159 <;> norm_num
  let x249 : ℝ := -y
  have hx249 : Bounds (-7441 / 40000) (-92803 / 500000) x249 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x250 : ℝ := x248+x249
  have hx250 : Bounds (1645309647 / 200000000000) (9123791669 / 1000000000000) x250 := by
    apply bounds_add hx248 hx249 <;> norm_num
  let x251 : ℝ := x248-y
  have hx251 : Bounds (1645309647 / 200000000000) (9123791669 / 1000000000000) x251 := by
    exact hx250
  let x252 : ℝ := x240*x240
  have hx252 : Bounds (6572795679 / 200000000000) (33026709611 / 1000000000000) x252 := by
    apply bounds_mul hx240 hx240 <;> norm_num
  let x253 : ℝ := x252⁻¹
  have hx253 : Bounds (3027852340661 / 100000000000) (30428452331023 / 1000000000000) x253 := by
    apply bounds_inv hx252 <;> norm_num
  let x254 : ℝ := x251*x253
  have hx254 : Bounds (249087733289 / 1000000000000) (277622859879 / 1000000000000) x254 := by
    apply bounds_mul hx251 hx253 <;> norm_num
  let x255 : ℝ := x251/x252
  have hx255 : Bounds (249087733289 / 1000000000000) (277622859879 / 1000000000000) x255 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx254
  let x256 : ℝ := (-2 / 1)*x255
  have hx256 : Bounds (-277622859879 / 500000000000) (-249087733289 / 500000000000) x256 := by
    apply bounds_mul (bounds_const ((-2 / 1) : ℝ)) hx255 <;> norm_num
  let x257 : ℝ := x256*x228
  have hx257 : Bounds (-794157444321 / 1000000000000) (-709222816807 / 1000000000000) x257 := by
    apply bounds_mul hx256 hx228 <;> norm_num
  let x258 : ℝ := (2 / 1)*x182
  have hx258 : Bounds (87750561 / 62500000) (175511419 / 125000000) x258 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx182 <;> norm_num
  let x259 : ℝ := c*c
  have hx259 : Bounds (17558635081 / 1000000000000) (4409889649 / 250000000000) x259 := by
    apply bounds_mul hc hc <;> norm_num
  let x260 : ℝ := -x259
  have hx260 : Bounds (-4409889649 / 250000000000) (-17558635081 / 1000000000000) x260 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx259
  let x261 : ℝ := x258+x260
  have hx261 : Bounds (346592354351 / 250000000000) (1386532716919 / 1000000000000) x261 := by
    apply bounds_add hx258 hx260 <;> norm_num
  let x262 : ℝ := x258-x259
  have hx262 : Bounds (346592354351 / 250000000000) (1386532716919 / 1000000000000) x262 := by
    exact hx261
  let x263 : ℝ := c*x262
  have hx263 : Bounds (18370642513 / 100000000000) (36830191253 / 200000000000) x263 := by
    apply bounds_mul hc hx262 <;> norm_num
  let x264 : ℝ := x245*x245
  have hx264 : Bounds (475577728713 / 1000000000000) (475711901911 / 1000000000000) x264 := by
    apply bounds_mul hx245 hx245 <;> norm_num
  let x265 : ℝ := x264⁻¹
  have hx265 : Bounds (262764079473 / 125000000000) (1051352848993 / 500000000000) x265 := by
    apply bounds_inv hx264 <;> norm_num
  let x266 : ℝ := x263*x265
  have hx266 : Bounds (19308579877 / 50000000000) (96803816257 / 250000000000) x266 := by
    apply bounds_mul hx263 hx265 <;> norm_num
  let x267 : ℝ := x263/x264
  have hx267 : Bounds (19308579877 / 50000000000) (96803816257 / 250000000000) x267 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx266
  let x268 : ℝ := (2 / 1)*x267
  have hx268 : Bounds (19308579877 / 25000000000) (96803816257 / 125000000000) x268 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx267 <;> norm_num
  let x269 : ℝ := x268*x235
  have hx269 : Bounds (801821455369 / 1000000000000) (804402264603 / 1000000000000) x269 := by
    apply bounds_mul hx268 hx235 <;> norm_num
  let x270 : ℝ := x257+x269
  have hx270 : Bounds (958001381 / 125000000000) (23794861949 / 250000000000) x270 := by
    apply bounds_add hx257 hx269 <;> norm_num
  have hPos : 0 < x270 :=
    lt_of_lt_of_le (by norm_num) hx270.1
  have hBridgeL : doubleCapBridgeL x = x48 := by
    exact hEll'
  rw [← doubleCapBridgeDerivativeTraceForm_eq x]
  simpa +zetaDelta only [doubleCapBridgeDerivativeTraceForm,
    hBridgeL, SmallMean.A, biasB, div_one, pow_two] using hPos

theorem acceptedCell : DoubleCapBridgeDerivativeCellCertificate
    (⟨20, by decide⟩ : Fin 256) doubleCapBridgeDerivativeExpression where
  positive x hx := by
    have hloEq : doubleCapBridgeLo (⟨20, by decide⟩ : Fin 256) =
        (67 / 512) := by norm_num [doubleCapBridgeLo, doubleCapBridgeStep]
    have hhiEq : doubleCapBridgeHi (⟨20, by decide⟩ : Fin 256) =
        (1343 / 10240) := by norm_num [doubleCapBridgeHi, doubleCapBridgeStep]
    have hlo : (67 / 512) ≤ x := by
      simpa only [hloEq] using hx.1
    have hhi : x ≤ (1343 / 10240) := by
      simpa only [hhiEq] using hx.2
    exact cell_derivative_pos x ⟨hlo, hhi⟩

#print axioms cell_derivative_pos
#print axioms acceptedCell

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell020

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell021 =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell021
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_derivative_pos (x : ℝ)
    (hx : Bounds (1343 / 10240) (673 / 5120) x) :
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
  have hx0 : Bounds (1343 / 5120) (673 / 2560) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx <;> norm_num
  let x1 : ℝ := Real.log (2 / 1)
  have hx1 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x1 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x2 : ℝ := Real.log (2 / 1)
  have hx2 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x2 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x3 : ℝ := (1 / 1)+(673 / 2560)
  have hx3 : Bounds (3233 / 2560) (3233 / 2560) x3 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((673 / 2560) : ℝ)) <;> norm_num
  let x4 : ℝ := (1 / 1)+(673 / 2560)
  have hx4 : Bounds (3233 / 2560) (3233 / 2560) x4 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((673 / 2560) : ℝ)) <;> norm_num
  let x5 : ℝ := Real.log x4
  have hx5 : Bounds (5835081 / 25000000) (233403241 / 1000000000) x5 := by
    exact bounds_log hx4 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x6 : ℝ := x3*x5
  have hx6 : Bounds (7369069091 / 25000000000) (36845345613 / 125000000000) x6 := by
    apply bounds_mul hx3 hx5 <;> norm_num
  let x7 : ℝ := -(673 / 2560)
  have hx7 : Bounds (-673 / 2560) (-673 / 2560) x7 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((673 / 2560) : ℝ))
  let x8 : ℝ := (1 / 1)+x7
  have hx8 : Bounds (1887 / 2560) (1887 / 2560) x8 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx7 <;> norm_num
  let x9 : ℝ := (1 / 1)-(673 / 2560)
  have hx9 : Bounds (1887 / 2560) (1887 / 2560) x9 := by
    exact hx8
  let x10 : ℝ := -(673 / 2560)
  have hx10 : Bounds (-673 / 2560) (-673 / 2560) x10 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((673 / 2560) : ℝ))
  let x11 : ℝ := (1 / 1)+x10
  have hx11 : Bounds (1887 / 2560) (1887 / 2560) x11 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx10 <;> norm_num
  let x12 : ℝ := (1 / 1)-(673 / 2560)
  have hx12 : Bounds (1887 / 2560) (1887 / 2560) x12 := by
    exact hx11
  let x13 : ℝ := Real.log x12
  have hx13 : Bounds (-305018993 / 1000000000) (-19063687 / 62500000) x13 := by
    exact bounds_log hx12 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x14 : ℝ := x9*x13
  have hx14 : Bounds (-112416179647 / 500000000000) (-56208089639 / 250000000000) x14 := by
    apply bounds_mul hx9 hx13 <;> norm_num
  let x15 : ℝ := x6+x14
  have hx15 : Bounds (34965202173 / 500000000000) (17482601587 / 250000000000) x15 := by
    apply bounds_add hx6 hx14 <;> norm_num
  let x16 : ℝ := (2 / 1)⁻¹
  have hx16 : Bounds (1 / 2) (1 / 2) x16 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x17 : ℝ := x15*x16
  have hx17 : Bounds (34965202173 / 1000000000000) (17482601587 / 500000000000) x17 := by
    apply bounds_mul hx15 hx16 <;> norm_num
  let x18 : ℝ := x15/(2 / 1)
  have hx18 : Bounds (34965202173 / 1000000000000) (17482601587 / 500000000000) x18 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx17
  let x19 : ℝ := -x18
  have hx19 : Bounds (-17482601587 / 500000000000) (-34965202173 / 1000000000000) x19 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx18
  let x20 : ℝ := x2+x19
  have hx20 : Bounds (329090988413 / 500000000000) (658181978827 / 1000000000000) x20 := by
    apply bounds_add hx2 hx19 <;> norm_num
  let x21 : ℝ := x2-x18
  have hx21 : Bounds (329090988413 / 500000000000) (658181978827 / 1000000000000) x21 := by
    exact hx20
  let x22 : ℝ := biasE (673 / 2560)
  have hx22 : Bounds (329090988413 / 500000000000) (658181978827 / 1000000000000) x22 := by
    simpa +zetaDelta only [biasE, div_one] using hx21
  let x23 : ℝ := Real.log (2 / 1)
  have hx23 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x23 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x24 : ℝ := (1 / 1)+(1343 / 5120)
  have hx24 : Bounds (6463 / 5120) (6463 / 5120) x24 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1343 / 5120) : ℝ)) <;> norm_num
  let x25 : ℝ := (1 / 1)+(1343 / 5120)
  have hx25 : Bounds (6463 / 5120) (6463 / 5120) x25 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1343 / 5120) : ℝ)) <;> norm_num
  let x26 : ℝ := Real.log x25
  have hx26 : Bounds (232939167 / 1000000000) (7279349 / 31250000) x26 := by
    exact bounds_log hx25 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x27 : ℝ := x24*x26
  have hx27 : Bounds (147020101203 / 500000000000) (294040203669 / 1000000000000) x27 := by
    apply bounds_mul hx24 hx26 <;> norm_num
  let x28 : ℝ := -(1343 / 5120)
  have hx28 : Bounds (-1343 / 5120) (-1343 / 5120) x28 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1343 / 5120) : ℝ))
  let x29 : ℝ := (1 / 1)+x28
  have hx29 : Bounds (3777 / 5120) (3777 / 5120) x29 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx28 <;> norm_num
  let x30 : ℝ := (1 / 1)-(1343 / 5120)
  have hx30 : Bounds (3777 / 5120) (3777 / 5120) x30 := by
    exact hx29
  let x31 : ℝ := -(1343 / 5120)
  have hx31 : Bounds (-1343 / 5120) (-1343 / 5120) x31 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1343 / 5120) : ℝ))
  let x32 : ℝ := (1 / 1)+x31
  have hx32 : Bounds (3777 / 5120) (3777 / 5120) x32 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx31 <;> norm_num
  let x33 : ℝ := (1 / 1)-(1343 / 5120)
  have hx33 : Bounds (3777 / 5120) (3777 / 5120) x33 := by
    exact hx32
  let x34 : ℝ := Real.log x33
  have hx34 : Bounds (-76056099 / 250000000) (-60844879 / 200000000) x34 := by
    exact bounds_log hx33 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x35 : ℝ := x30*x34
  have hx35 : Bounds (-112212455439 / 500000000000) (-224424910139 / 1000000000000) x35 := by
    apply bounds_mul hx30 hx34 <;> norm_num
  let x36 : ℝ := x27+x35
  have hx36 : Bounds (8701911441 / 125000000000) (6961529353 / 100000000000) x36 := by
    apply bounds_add hx27 hx35 <;> norm_num
  let x37 : ℝ := (2 / 1)⁻¹
  have hx37 : Bounds (1 / 2) (1 / 2) x37 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x38 : ℝ := x36*x37
  have hx38 : Bounds (8701911441 / 250000000000) (6961529353 / 200000000000) x38 := by
    apply bounds_mul hx36 hx37 <;> norm_num
  let x39 : ℝ := x36/(2 / 1)
  have hx39 : Bounds (8701911441 / 250000000000) (6961529353 / 200000000000) x39 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx38
  let x40 : ℝ := -x39
  have hx40 : Bounds (-6961529353 / 200000000000) (-8701911441 / 250000000000) x40 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx39
  let x41 : ℝ := x23+x40
  have hx41 : Bounds (131667906647 / 200000000000) (164584883809 / 250000000000) x41 := by
    apply bounds_add hx23 hx40 <;> norm_num
  let x42 : ℝ := x23-x39
  have hx42 : Bounds (131667906647 / 200000000000) (164584883809 / 250000000000) x42 := by
    exact hx41
  let x43 : ℝ := biasE (1343 / 5120)
  have hx43 : Bounds (131667906647 / 200000000000) (164584883809 / 250000000000) x43 := by
    simpa +zetaDelta only [biasE, div_one] using hx42
  let x44 : ℝ := biasE x0
  have hx44 : Bounds (329090988413 / 500000000000) (164584883809 / 250000000000) x44 := by
    exact bounds_biasE hx0 (by norm_num) (by norm_num) hx22.1 hx43.2
  let x45 : ℝ := x1+x44
  have hx45 : Bounds (675664578413 / 500000000000) (337871679059 / 250000000000) x45 := by
    apply bounds_add hx1 hx44 <;> norm_num
  let x46 : ℝ := (2 / 1)⁻¹
  have hx46 : Bounds (1 / 2) (1 / 2) x46 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x47 : ℝ := x45*x46
  have hx47 : Bounds (675664578413 / 1000000000000) (337871679059 / 500000000000) x47 := by
    apply bounds_mul hx45 hx46 <;> norm_num
  let x48 : ℝ := x45/(2 / 1)
  have hx48 : Bounds (675664578413 / 1000000000000) (337871679059 / 500000000000) x48 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx47
  let x49 : ℝ := Real.log (2 / 1)
  have hx49 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x49 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x50 : ℝ := (1 / 1)+(23253 / 125000)
  have hx50 : Bounds (148253 / 125000) (148253 / 125000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((23253 / 125000) : ℝ)) <;> norm_num
  let x51 : ℝ := (1 / 1)+(23253 / 125000)
  have hx51 : Bounds (148253 / 125000) (148253 / 125000) x51 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((23253 / 125000) : ℝ)) <;> norm_num
  let x52 : ℝ := Real.log x51
  have hx52 : Bounds (21325817 / 125000000) (170606537 / 1000000000) x52 := by
    exact bounds_log hx51 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x53 : ℝ := x50*x52
  have hx53 : Bounds (50585861563 / 250000000000) (202343447439 / 1000000000000) x53 := by
    apply bounds_mul hx50 hx52 <;> norm_num
  let x54 : ℝ := -(23253 / 125000)
  have hx54 : Bounds (-23253 / 125000) (-23253 / 125000) x54 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((23253 / 125000) : ℝ))
  let x55 : ℝ := (1 / 1)+x54
  have hx55 : Bounds (101747 / 125000) (101747 / 125000) x55 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx54 <;> norm_num
  let x56 : ℝ := (1 / 1)-(23253 / 125000)
  have hx56 : Bounds (101747 / 125000) (101747 / 125000) x56 := by
    exact hx55
  let x57 : ℝ := -(23253 / 125000)
  have hx57 : Bounds (-23253 / 125000) (-23253 / 125000) x57 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((23253 / 125000) : ℝ))
  let x58 : ℝ := (1 / 1)+x57
  have hx58 : Bounds (101747 / 125000) (101747 / 125000) x58 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx57 <;> norm_num
  let x59 : ℝ := (1 / 1)-(23253 / 125000)
  have hx59 : Bounds (101747 / 125000) (101747 / 125000) x59 := by
    exact hx58
  let x60 : ℝ := Real.log x59
  have hx60 : Bounds (-102912199 / 500000000) (-205824397 / 1000000000) x60 := by
    exact bounds_log hx59 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x61 : ℝ := x56*x60
  have hx61 : Bounds (-167536120187 / 1000000000000) (-41884029843 / 250000000000) x61 := by
    apply bounds_mul hx56 hx60 <;> norm_num
  let x62 : ℝ := x53+x61
  have hx62 : Bounds (6961465213 / 200000000000) (34807328067 / 1000000000000) x62 := by
    apply bounds_add hx53 hx61 <;> norm_num
  let x63 : ℝ := (2 / 1)⁻¹
  have hx63 : Bounds (1 / 2) (1 / 2) x63 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x64 : ℝ := x62*x63
  have hx64 : Bounds (2175457879 / 125000000000) (8701832017 / 500000000000) x64 := by
    apply bounds_mul hx62 hx63 <;> norm_num
  let x65 : ℝ := x62/(2 / 1)
  have hx65 : Bounds (2175457879 / 125000000000) (8701832017 / 500000000000) x65 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx64
  let x66 : ℝ := -x65
  have hx66 : Bounds (-8701832017 / 500000000000) (-2175457879 / 125000000000) x66 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx65
  let x67 : ℝ := x49+x66
  have hx67 : Bounds (337871757983 / 500000000000) (42233969873 / 62500000000) x67 := by
    apply bounds_add hx49 hx66 <;> norm_num
  let x68 : ℝ := x49-x65
  have hx68 : Bounds (337871757983 / 500000000000) (42233969873 / 62500000000) x68 := by
    exact hx67
  let x69 : ℝ := biasE (23253 / 125000)
  have hx69 : Bounds (337871757983 / 500000000000) (42233969873 / 62500000000) x69 := by
    simpa +zetaDelta only [biasE, div_one] using hx68
  let x70 : ℝ := Real.log (2 / 1)
  have hx70 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x70 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x71 : ℝ := (1 / 1)+(186443 / 1000000)
  have hx71 : Bounds (1186443 / 1000000) (1186443 / 1000000) x71 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((186443 / 1000000) : ℝ)) <;> norm_num
  let x72 : ℝ := (1 / 1)+(186443 / 1000000)
  have hx72 : Bounds (1186443 / 1000000) (1186443 / 1000000) x72 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((186443 / 1000000) : ℝ)) <;> norm_num
  let x73 : ℝ := Real.log x72
  have hx73 : Bounds (34191951 / 200000000) (42739939 / 250000000) x73 := by
    exact bounds_log hx72 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x74 : ℝ := x71*x73
  have hx74 : Bounds (202834004601 / 1000000000000) (50708501447 / 250000000000) x74 := by
    apply bounds_mul hx71 hx73 <;> norm_num
  let x75 : ℝ := -(186443 / 1000000)
  have hx75 : Bounds (-186443 / 1000000) (-186443 / 1000000) x75 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((186443 / 1000000) : ℝ))
  let x76 : ℝ := (1 / 1)+x75
  have hx76 : Bounds (813557 / 1000000) (813557 / 1000000) x76 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx75 <;> norm_num
  let x77 : ℝ := (1 / 1)-(186443 / 1000000)
  have hx77 : Bounds (813557 / 1000000) (813557 / 1000000) x77 := by
    exact hx76
  let x78 : ℝ := -(186443 / 1000000)
  have hx78 : Bounds (-186443 / 1000000) (-186443 / 1000000) x78 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((186443 / 1000000) : ℝ))
  let x79 : ℝ := (1 / 1)+x78
  have hx79 : Bounds (813557 / 1000000) (813557 / 1000000) x79 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx78 <;> norm_num
  let x80 : ℝ := (1 / 1)-(186443 / 1000000)
  have hx80 : Bounds (813557 / 1000000) (813557 / 1000000) x80 := by
    exact hx79
  let x81 : ℝ := Real.log x80
  have hx81 : Bounds (-25792411 / 125000000) (-206339287 / 1000000000) x81 := by
    exact bounds_log hx80 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x82 : ℝ := x77*x81
  have hx82 : Bounds (-5245899129 / 31250000000) (-167868771313 / 1000000000000) x82 := by
    apply bounds_mul hx77 hx81 <;> norm_num
  let x83 : ℝ := x74+x82
  have hx83 : Bounds (34965232473 / 1000000000000) (1398609379 / 40000000000) x83 := by
    apply bounds_add hx74 hx82 <;> norm_num
  let x84 : ℝ := (2 / 1)⁻¹
  have hx84 : Bounds (1 / 2) (1 / 2) x84 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x85 : ℝ := x83*x84
  have hx85 : Bounds (4370654059 / 250000000000) (8741308619 / 500000000000) x85 := by
    apply bounds_mul hx83 hx84 <;> norm_num
  let x86 : ℝ := x83/(2 / 1)
  have hx86 : Bounds (4370654059 / 250000000000) (8741308619 / 500000000000) x86 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx85
  let x87 : ℝ := -x86
  have hx87 : Bounds (-8741308619 / 500000000000) (-4370654059 / 250000000000) x87 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx86
  let x88 : ℝ := x70+x87
  have hx88 : Bounds (337832281381 / 500000000000) (168916141191 / 250000000000) x88 := by
    apply bounds_add hx70 hx87 <;> norm_num
  let x89 : ℝ := x70-x86
  have hx89 : Bounds (337832281381 / 500000000000) (168916141191 / 250000000000) x89 := by
    exact hx88
  let x90 : ℝ := biasE (186443 / 1000000)
  have hx90 : Bounds (337832281381 / 500000000000) (168916141191 / 250000000000) x90 := by
    simpa +zetaDelta only [biasE, div_one] using hx89
  let y : ℝ := doubleCapHighTailY x
  have hEll' : Real.log 2 * doubleCapHighTailFloor x = x48 := by
    simpa +zetaDelta only [div_one] using hEll
  have hy : Bounds (23253 / 125000) (186443 / 1000000) y := by
    dsimp only [y, doubleCapHighTailY]
    apply entropyInverseBias_bracket hh0.le hh1.le
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (186443 / 1000000) ≤ (168916141191 / 250000000000) := hx90.2
      have h2 : (675664578413 / 1000000000000) ≤ x48 := hx48.1
      linarith [hEll']
    · have h1 : x48 ≤ (337871679059 / 500000000000) := hx48.2
      have h2 : (337871757983 / 500000000000) ≤ biasE (23253 / 125000) := hx69.1
      linarith [hEll']
  let x91 : ℝ := x⁻¹
  have hx91 : Bounds (304309063893 / 40000000000) (3812360387193 / 500000000000) x91 := by
    apply bounds_inv hx <;> norm_num
  let x92 : ℝ := x48*x91
  have hx92 : Bounds (2570135692031 / 500000000000) (1288088605199 / 250000000000) x92 := by
    apply bounds_mul hx48 hx91 <;> norm_num
  let x93 : ℝ := x48/x
  have hx93 : Bounds (2570135692031 / 500000000000) (1288088605199 / 250000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(132813 / 1000000)
  have hx95 : Bounds (1132813 / 1000000) (1132813 / 1000000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((132813 / 1000000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(132813 / 1000000)
  have hx96 : Bounds (1132813 / 1000000) (1132813 / 1000000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((132813 / 1000000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (124703919 / 1000000000) (1558799 / 12500000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (70633110297 / 500000000000) (141266221727 / 1000000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(132813 / 1000000)
  have hx99 : Bounds (-132813 / 1000000) (-132813 / 1000000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((132813 / 1000000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (867187 / 1000000) (867187 / 1000000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(132813 / 1000000)
  have hx101 : Bounds (867187 / 1000000) (867187 / 1000000) x101 := by
    exact hx100
  let x102 : ℝ := -(132813 / 1000000)
  have hx102 : Bounds (-132813 / 1000000) (-132813 / 1000000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((132813 / 1000000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (867187 / 1000000) (867187 / 1000000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(132813 / 1000000)
  have hx104 : Bounds (867187 / 1000000) (867187 / 1000000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-890629 / 6250000) (-142500639 / 1000000000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-49429881 / 400000000) (-1930854713 / 15625000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (8845759047 / 500000000000) (3538304019 / 200000000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (8845759047 / 1000000000000) (552860003 / 62500000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (8845759047 / 1000000000000) (552860003 / 62500000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-552860003 / 62500000000) (-8845759047 / 1000000000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (42768838747 / 62500000000) (684301421953 / 1000000000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (42768838747 / 62500000000) (684301421953 / 1000000000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (132813 / 1000000)
  have hx114 : Bounds (42768838747 / 62500000000) (684301421953 / 1000000000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(66559 / 500000)
  have hx116 : Bounds (566559 / 500000) (566559 / 500000) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((66559 / 500000) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(66559 / 500000)
  have hx117 : Bounds (566559 / 500000) (566559 / 500000) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((66559 / 500000) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (31243281 / 250000000) (199957 / 1600000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (442529051 / 3125000000) (70804648727 / 500000000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(66559 / 500000)
  have hx120 : Bounds (-66559 / 500000) (-66559 / 500000) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((66559 / 500000) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (433441 / 500000) (433441 / 500000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(66559 / 500000)
  have hx122 : Bounds (433441 / 500000) (433441 / 500000) x122 := by
    exact hx121
  let x123 : ℝ := -(66559 / 500000)
  have hx123 : Bounds (-66559 / 500000) (-66559 / 500000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((66559 / 500000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (433441 / 500000) (433441 / 500000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(66559 / 500000)
  have hx125 : Bounds (433441 / 500000) (433441 / 500000) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-142852413 / 1000000000) (-35713103 / 250000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-123836185487 / 1000000000000) (-123836184619 / 1000000000000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (17773110833 / 1000000000000) (3554622567 / 200000000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (1110819427 / 125000000000) (4443278209 / 500000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (1110819427 / 125000000000) (4443278209 / 500000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-4443278209 / 500000000000) (-1110819427 / 125000000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (342130311791 / 500000000000) (42766289099 / 62500000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (342130311791 / 500000000000) (42766289099 / 62500000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (66559 / 500000)
  have hx135 : Bounds (342130311791 / 500000000000) (42766289099 / 62500000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(132813 / 1000000)
  have hx136 : Bounds (682694863331 / 1000000000000) (68429964769 / 100000000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((132813 / 1000000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(66559 / 500000)
  have hx137 : Bounds (684262646103 / 1000000000000) (171467778947 / 250000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((66559 / 500000) : ℝ)) <;> norm_num
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
  have hc : Bounds (132813 / 1000000) (66559 / 500000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num)
      (by norm_num) (show 0 < x93 by linarith [hx93.1]) hcEq
    · have h1 : x93 * (132813 / 1000000) ≤ (68429964769 / 100000000000) := hx136.2
      have h2 : (42768838747 / 62500000000) ≤ biasE (132813 / 1000000) := hx114.1
      linarith
    · have h1 : biasE (66559 / 500000) ≤ (42766289099 / 62500000000) := hx135.2
      have h2 : (684262646103 / 1000000000000) ≤ x93 * (66559 / 500000) := hx137.1
      linarith
  let x138 : ℝ := (1 / 1)+x0
  have hx138 : Bounds (6463 / 5120) (3233 / 2560) x138 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx0 <;> norm_num
  let x139 : ℝ := -x0
  have hx139 : Bounds (-673 / 2560) (-1343 / 5120) x139 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x140 : ℝ := (1 / 1)+x139
  have hx140 : Bounds (1887 / 2560) (3777 / 5120) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx139 <;> norm_num
  let x141 : ℝ := (1 / 1)-x0
  have hx141 : Bounds (1887 / 2560) (3777 / 5120) x141 := by
    exact hx140
  let x142 : ℝ := x141⁻¹
  have hx142 : Bounds (169446650781 / 125000000000) (42395336513 / 31250000000) x142 := by
    apply bounds_inv hx141 <;> norm_num
  let x143 : ℝ := x138*x142
  have hx143 : Bounds (106946650781 / 62500000000) (26770336513 / 15625000000) x143 := by
    apply bounds_mul hx138 hx142 <;> norm_num
  let x144 : ℝ := x138/x141
  have hx144 : Bounds (106946650781 / 62500000000) (26770336513 / 15625000000) x144 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx143
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (268581781 / 500000000) (538422233 / 1000000000) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_14.2)
  let x146 : ℝ := (2 / 1)⁻¹
  have hx146 : Bounds (1 / 2) (1 / 2) x146 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x147 : ℝ := x145*x146
  have hx147 : Bounds (268581781 / 1000000000) (538422233 / 2000000000) x147 := by
    apply bounds_mul hx145 hx146 <;> norm_num
  let x148 : ℝ := x145/(2 / 1)
  have hx148 : Bounds (268581781 / 1000000000) (538422233 / 2000000000) x148 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx147
  let x149 : ℝ := (1 / 1)+y
  have hx149 : Bounds (148253 / 125000) (1186443 / 1000000) x149 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x150 : ℝ := -y
  have hx150 : Bounds (-186443 / 1000000) (-23253 / 125000) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (813557 / 1000000) (101747 / 125000) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-y
  have hx152 : Bounds (813557 / 1000000) (101747 / 125000) x152 := by
    exact hx151
  let x153 : ℝ := x152⁻¹
  have hx153 : Bounds (245707490147 / 200000000000) (307292543731 / 250000000000) x153 := by
    apply bounds_inv hx152 <;> norm_num
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (145707490147 / 100000000000) (182292543731 / 125000000000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x149/x152
  have hx155 : Bounds (145707490147 / 100000000000) (182292543731 / 125000000000) x155 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx154
  let x156 : ℝ := Real.log x155
  have hx156 : Bounds (376430933 / 1000000000) (377299043 / 1000000000) x156 := by
    exact bounds_log hx155 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_16.2)
  let x157 : ℝ := (2 / 1)⁻¹
  have hx157 : Bounds (1 / 2) (1 / 2) x157 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x158 : ℝ := x156*x157
  have hx158 : Bounds (376430933 / 2000000000) (377299043 / 2000000000) x158 := by
    apply bounds_mul hx156 hx157 <;> norm_num
  let x159 : ℝ := x156/(2 / 1)
  have hx159 : Bounds (376430933 / 2000000000) (377299043 / 2000000000) x159 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx158
  let x160 : ℝ := (1 / 1)+c
  have hx160 : Bounds (1132813 / 1000000) (566559 / 500000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x161 : ℝ := -c
  have hx161 : Bounds (-66559 / 500000) (-132813 / 1000000) x161 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x162 : ℝ := (1 / 1)+x161
  have hx162 : Bounds (433441 / 500000) (867187 / 1000000) x162 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx161 <;> norm_num
  let x163 : ℝ := (1 / 1)-c
  have hx163 : Bounds (433441 / 500000) (867187 / 1000000) x163 := by
    exact hx162
  let x164 : ℝ := x163⁻¹
  have hx164 : Bounds (576576909017 / 500000000000) (1153559538669 / 1000000000000) x164 := by
    apply bounds_inv hx163 <;> norm_num
  let x165 : ℝ := x160*x164
  have hx165 : Bounds (326576909017 / 250000000000) (653559538669 / 500000000000) x165 := by
    apply bounds_mul hx160 hx164 <;> norm_num
  let x166 : ℝ := x160/x163
  have hx166 : Bounds (326576909017 / 250000000000) (653559538669 / 500000000000) x166 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx165
  let x167 : ℝ := Real.log x166
  have hx167 : Bounds (267204559 / 1000000000) (133912769 / 500000000) x167 := by
    exact bounds_log hx166 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x168 : ℝ := (2 / 1)⁻¹
  have hx168 : Bounds (1 / 2) (1 / 2) x168 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x169 : ℝ := x167*x168
  have hx169 : Bounds (267204559 / 2000000000) (133912769 / 1000000000) x169 := by
    apply bounds_mul hx167 hx168 <;> norm_num
  let x170 : ℝ := x167/(2 / 1)
  have hx170 : Bounds (267204559 / 2000000000) (133912769 / 1000000000) x170 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx169
  let x171 : ℝ := Real.log (2 / 1)
  have hx171 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x171 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x172 : ℝ := c*c
  have hx172 : Bounds (17639292969 / 1000000000000) (4430100481 / 250000000000) x172 := by
    apply bounds_mul hc hc <;> norm_num
  let x173 : ℝ := -x172
  have hx173 : Bounds (-4430100481 / 250000000000) (-17639292969 / 1000000000000) x173 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx172
  let x174 : ℝ := (1 / 1)+x173
  have hx174 : Bounds (245569899519 / 250000000000) (982360707031 / 1000000000000) x174 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx173 <;> norm_num
  let x175 : ℝ := (1 / 1)-x172
  have hx175 : Bounds (245569899519 / 250000000000) (982360707031 / 1000000000000) x175 := by
    exact hx174
  let x176 : ℝ := Real.log x175
  have hx176 : Bounds (-17879289 / 1000000000) (-17796719 / 1000000000) x176 := by
    exact bounds_log hx175 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (-17879289 / 2000000000) (-17796719 / 2000000000) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (-17879289 / 2000000000) (-17796719 / 2000000000) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (17796719 / 2000000000) (17879289 / 2000000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x171+x180
  have hx181 : Bounds (1404091079 / 2000000000) (1404173651 / 2000000000) x181 := by
    apply bounds_add hx171 hx180 <;> norm_num
  let x182 : ℝ := x171-x179
  have hx182 : Bounds (1404091079 / 2000000000) (1404173651 / 2000000000) x182 := by
    exact hx181
  let x183 : ℝ := Real.log (2 / 1)
  have hx183 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x183 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x184 : ℝ := (1 / 1)+(66559 / 500000)
  have hx184 : Bounds (566559 / 500000) (566559 / 500000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((66559 / 500000) : ℝ)) <;> norm_num
  let x185 : ℝ := (1 / 1)+(66559 / 500000)
  have hx185 : Bounds (566559 / 500000) (566559 / 500000) x185 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((66559 / 500000) : ℝ)) <;> norm_num
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (31243281 / 250000000) (199957 / 1600000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x187 : ℝ := x184*x186
  have hx187 : Bounds (442529051 / 3125000000) (70804648727 / 500000000000) x187 := by
    apply bounds_mul hx184 hx186 <;> norm_num
  let x188 : ℝ := -(66559 / 500000)
  have hx188 : Bounds (-66559 / 500000) (-66559 / 500000) x188 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((66559 / 500000) : ℝ))
  let x189 : ℝ := (1 / 1)+x188
  have hx189 : Bounds (433441 / 500000) (433441 / 500000) x189 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx188 <;> norm_num
  let x190 : ℝ := (1 / 1)-(66559 / 500000)
  have hx190 : Bounds (433441 / 500000) (433441 / 500000) x190 := by
    exact hx189
  let x191 : ℝ := -(66559 / 500000)
  have hx191 : Bounds (-66559 / 500000) (-66559 / 500000) x191 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((66559 / 500000) : ℝ))
  let x192 : ℝ := (1 / 1)+x191
  have hx192 : Bounds (433441 / 500000) (433441 / 500000) x192 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx191 <;> norm_num
  let x193 : ℝ := (1 / 1)-(66559 / 500000)
  have hx193 : Bounds (433441 / 500000) (433441 / 500000) x193 := by
    exact hx192
  let x194 : ℝ := Real.log x193
  have hx194 : Bounds (-142852413 / 1000000000) (-35713103 / 250000000) x194 := by
    exact bounds_log hx193 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x195 : ℝ := x190*x194
  have hx195 : Bounds (-123836185487 / 1000000000000) (-123836184619 / 1000000000000) x195 := by
    apply bounds_mul hx190 hx194 <;> norm_num
  let x196 : ℝ := x187+x195
  have hx196 : Bounds (17773110833 / 1000000000000) (3554622567 / 200000000000) x196 := by
    apply bounds_add hx187 hx195 <;> norm_num
  let x197 : ℝ := (2 / 1)⁻¹
  have hx197 : Bounds (1 / 2) (1 / 2) x197 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x198 : ℝ := x196*x197
  have hx198 : Bounds (1110819427 / 125000000000) (4443278209 / 500000000000) x198 := by
    apply bounds_mul hx196 hx197 <;> norm_num
  let x199 : ℝ := x196/(2 / 1)
  have hx199 : Bounds (1110819427 / 125000000000) (4443278209 / 500000000000) x199 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx198
  let x200 : ℝ := -x199
  have hx200 : Bounds (-4443278209 / 500000000000) (-1110819427 / 125000000000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx199
  let x201 : ℝ := x183+x200
  have hx201 : Bounds (342130311791 / 500000000000) (42766289099 / 62500000000) x201 := by
    apply bounds_add hx183 hx200 <;> norm_num
  let x202 : ℝ := x183-x199
  have hx202 : Bounds (342130311791 / 500000000000) (42766289099 / 62500000000) x202 := by
    exact hx201
  let x203 : ℝ := biasE (66559 / 500000)
  have hx203 : Bounds (342130311791 / 500000000000) (42766289099 / 62500000000) x203 := by
    simpa +zetaDelta only [biasE, div_one] using hx202
  let x204 : ℝ := Real.log (2 / 1)
  have hx204 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x204 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x205 : ℝ := (1 / 1)+(132813 / 1000000)
  have hx205 : Bounds (1132813 / 1000000) (1132813 / 1000000) x205 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((132813 / 1000000) : ℝ)) <;> norm_num
  let x206 : ℝ := (1 / 1)+(132813 / 1000000)
  have hx206 : Bounds (1132813 / 1000000) (1132813 / 1000000) x206 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((132813 / 1000000) : ℝ)) <;> norm_num
  let x207 : ℝ := Real.log x206
  have hx207 : Bounds (124703919 / 1000000000) (1558799 / 12500000) x207 := by
    exact bounds_log hx206 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x208 : ℝ := x205*x207
  have hx208 : Bounds (70633110297 / 500000000000) (141266221727 / 1000000000000) x208 := by
    apply bounds_mul hx205 hx207 <;> norm_num
  let x209 : ℝ := -(132813 / 1000000)
  have hx209 : Bounds (-132813 / 1000000) (-132813 / 1000000) x209 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((132813 / 1000000) : ℝ))
  let x210 : ℝ := (1 / 1)+x209
  have hx210 : Bounds (867187 / 1000000) (867187 / 1000000) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx209 <;> norm_num
  let x211 : ℝ := (1 / 1)-(132813 / 1000000)
  have hx211 : Bounds (867187 / 1000000) (867187 / 1000000) x211 := by
    exact hx210
  let x212 : ℝ := -(132813 / 1000000)
  have hx212 : Bounds (-132813 / 1000000) (-132813 / 1000000) x212 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((132813 / 1000000) : ℝ))
  let x213 : ℝ := (1 / 1)+x212
  have hx213 : Bounds (867187 / 1000000) (867187 / 1000000) x213 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx212 <;> norm_num
  let x214 : ℝ := (1 / 1)-(132813 / 1000000)
  have hx214 : Bounds (867187 / 1000000) (867187 / 1000000) x214 := by
    exact hx213
  let x215 : ℝ := Real.log x214
  have hx215 : Bounds (-890629 / 6250000) (-142500639 / 1000000000) x215 := by
    exact bounds_log hx214 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x216 : ℝ := x211*x215
  have hx216 : Bounds (-49429881 / 400000000) (-1930854713 / 15625000000) x216 := by
    apply bounds_mul hx211 hx215 <;> norm_num
  let x217 : ℝ := x208+x216
  have hx217 : Bounds (8845759047 / 500000000000) (3538304019 / 200000000000) x217 := by
    apply bounds_add hx208 hx216 <;> norm_num
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (8845759047 / 1000000000000) (552860003 / 62500000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (8845759047 / 1000000000000) (552860003 / 62500000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := -x220
  have hx221 : Bounds (-552860003 / 62500000000) (-8845759047 / 1000000000000) x221 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx220
  let x222 : ℝ := x204+x221
  have hx222 : Bounds (42768838747 / 62500000000) (684301421953 / 1000000000000) x222 := by
    apply bounds_add hx204 hx221 <;> norm_num
  let x223 : ℝ := x204-x220
  have hx223 : Bounds (42768838747 / 62500000000) (684301421953 / 1000000000000) x223 := by
    exact hx222
  let x224 : ℝ := biasE (132813 / 1000000)
  have hx224 : Bounds (42768838747 / 62500000000) (684301421953 / 1000000000000) x224 := by
    simpa +zetaDelta only [biasE, div_one] using hx223
  let x225 : ℝ := biasE c
  have hx225 : Bounds (342130311791 / 500000000000) (684301421953 / 1000000000000) x225 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx203.1 hx224.2
  let x226 : ℝ := x159⁻¹
  have hx226 : Bounds (5300835072619 / 1000000000000) (1328264911747 / 250000000000) x226 := by
    apply bounds_inv hx159 <;> norm_num
  let x227 : ℝ := x148*x226
  have hx227 : Bounds (1423707724591 / 1000000000000) (1430334719597 / 1000000000000) x227 := by
    apply bounds_mul hx148 hx226 <;> norm_num
  let x228 : ℝ := x148/x159
  have hx228 : Bounds (1423707724591 / 1000000000000) (1430334719597 / 1000000000000) x228 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx227
  let x229 : ℝ := c*x148
  have hx229 : Bounds (35671152079 / 1000000000000) (35836845407 / 1000000000000) x229 := by
    apply bounds_mul hc hx148 <;> norm_num
  let x230 : ℝ := x225+x229
  have hx230 : Bounds (719931775661 / 1000000000000) (4500864171 / 6250000000) x230 := by
    apply bounds_add hx225 hx229 <;> norm_num
  let x231 : ℝ := x*x170
  have hx231 : Bounds (8761126043 / 500000000000) (17602205769 / 1000000000000) x231 := by
    apply bounds_mul hx hx170 <;> norm_num
  let x232 : ℝ := x48+x231
  have hx232 : Bounds (693186830499 / 1000000000000) (693345563887 / 1000000000000) x232 := by
    apply bounds_add hx48 hx231 <;> norm_num
  let x233 : ℝ := x232⁻¹
  have hx233 : Bounds (1442282250129 / 1000000000000) (1442612519457 / 1000000000000) x233 := by
    apply bounds_inv hx232 <;> norm_num
  let x234 : ℝ := x230*x233
  have hx234 : Bounds (1038344821339 / 1000000000000) (519440240117 / 500000000000) x234 := by
    apply bounds_mul hx230 hx233 <;> norm_num
  let x235 : ℝ := x230/x232
  have hx235 : Bounds (1038344821339 / 1000000000000) (519440240117 / 500000000000) x235 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx234
  let x236 : ℝ := y*y
  have hx236 : Bounds (540702009 / 15625000000) (34760992249 / 1000000000000) x236 := by
    apply bounds_mul hy hy <;> norm_num
  let x237 : ℝ := -x236
  have hx237 : Bounds (-34760992249 / 1000000000000) (-540702009 / 15625000000) x237 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx236
  let x238 : ℝ := (1 / 1)+x237
  have hx238 : Bounds (965239007751 / 1000000000000) (15084297991 / 15625000000) x238 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx237 <;> norm_num
  let x239 : ℝ := (1 / 1)-x236
  have hx239 : Bounds (965239007751 / 1000000000000) (15084297991 / 15625000000) x239 := by
    exact hx238
  let x240 : ℝ := x239*x159
  have hx240 : Bounds (181672910127 / 1000000000000) (182121318283 / 1000000000000) x240 := by
    apply bounds_mul hx239 hx159 <;> norm_num
  let x241 : ℝ := c*c
  have hx241 : Bounds (17639292969 / 1000000000000) (4430100481 / 250000000000) x241 := by
    apply bounds_mul hc hc <;> norm_num
  let x242 : ℝ := -x241
  have hx242 : Bounds (-4430100481 / 250000000000) (-17639292969 / 1000000000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx241
  let x243 : ℝ := (1 / 1)+x242
  have hx243 : Bounds (245569899519 / 250000000000) (982360707031 / 1000000000000) x243 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx242 <;> norm_num
  let x244 : ℝ := (1 / 1)-x241
  have hx244 : Bounds (245569899519 / 250000000000) (982360707031 / 1000000000000) x244 := by
    exact hx243
  let x245 : ℝ := x244*x182
  have hx245 : Bounds (689605010371 / 1000000000000) (86212813787 / 125000000000) x245 := by
    apply bounds_mul hx244 hx182 <;> norm_num
  let x246 : ℝ := y*y
  have hx246 : Bounds (540702009 / 15625000000) (34760992249 / 1000000000000) x246 := by
    apply bounds_mul hy hy <;> norm_num
  let x247 : ℝ := (1 / 1)+x246
  have hx247 : Bounds (16165702009 / 15625000000) (1034760992249 / 1000000000000) x247 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx246 <;> norm_num
  let x248 : ℝ := x247*x159
  have hx248 : Bounds (7789145971 / 40000000000) (39041433211 / 200000000000) x248 := by
    apply bounds_mul hx247 hx159 <;> norm_num
  let x249 : ℝ := -y
  have hx249 : Bounds (-186443 / 1000000) (-23253 / 125000) x249 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x250 : ℝ := x248+x249
  have hx250 : Bounds (331425971 / 40000000000) (1836633211 / 200000000000) x250 := by
    apply bounds_add hx248 hx249 <;> norm_num
  let x251 : ℝ := x248-y
  have hx251 : Bounds (331425971 / 40000000000) (1836633211 / 200000000000) x251 := by
    exact hx250
  let x252 : ℝ := x240*x240
  have hx252 : Bounds (16502523137 / 500000000000) (16584087287 / 500000000000) x252 := by
    apply bounds_mul hx240 hx240 <;> norm_num
  let x253 : ℝ := x252⁻¹
  have hx253 : Bounds (30149383040931 / 1000000000000) (15149198575549 / 500000000000) x253 := by
    apply bounds_inv hx252 <;> norm_num
  let x254 : ℝ := x251*x253
  have hx254 : Bounds (124903606867 / 500000000000) (278235212239 / 1000000000000) x254 := by
    apply bounds_mul hx251 hx253 <;> norm_num
  let x255 : ℝ := x251/x252
  have hx255 : Bounds (124903606867 / 500000000000) (278235212239 / 1000000000000) x255 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx254
  let x256 : ℝ := (-2 / 1)*x255
  have hx256 : Bounds (-278235212239 / 500000000000) (-124903606867 / 250000000000) x256 := by
    apply bounds_mul (bounds_const ((-2 / 1) : ℝ)) hx255 <;> norm_num
  let x257 : ℝ := x256*x228
  have hx257 : Bounds (-9949237107 / 12500000000) (-711304919703 / 1000000000000) x257 := by
    apply bounds_mul hx256 hx228 <;> norm_num
  let x258 : ℝ := (2 / 1)*x182
  have hx258 : Bounds (1404091079 / 1000000000) (1404173651 / 1000000000) x258 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx182 <;> norm_num
  let x259 : ℝ := c*c
  have hx259 : Bounds (17639292969 / 1000000000000) (4430100481 / 250000000000) x259 := by
    apply bounds_mul hc hc <;> norm_num
  let x260 : ℝ := -x259
  have hx260 : Bounds (-4430100481 / 250000000000) (-17639292969 / 1000000000000) x260 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx259
  let x261 : ℝ := x258+x260
  have hx261 : Bounds (346592669269 / 250000000000) (1386534358031 / 1000000000000) x261 := by
    apply bounds_add hx258 hx260 <;> norm_num
  let x262 : ℝ := x258-x259
  have hx262 : Bounds (346592669269 / 250000000000) (1386534358031 / 1000000000000) x262 := by
    exact hx261
  let x263 : ℝ := c*x262
  have hx263 : Bounds (92064024367 / 500000000000) (184572680673 / 1000000000000) x263 := by
    apply bounds_mul hc hx262 <;> norm_num
  let x264 : ℝ := x245*x245
  have hx264 : Bounds (59444383791 / 125000000000) (475689552709 / 1000000000000) x264 := by
    apply bounds_mul hx245 hx245 <;> norm_num
  let x265 : ℝ := x264⁻¹
  have hx265 : Bounds (210221139881 / 100000000000) (525701470973 / 250000000000) x265 := by
    apply bounds_inv hx264 <;> norm_num
  let x266 : ℝ := x263*x265
  have hx266 : Bounds (387076082889 / 1000000000000) (15524820757 / 40000000000) x266 := by
    apply bounds_mul hx263 hx265 <;> norm_num
  let x267 : ℝ := x263/x264
  have hx267 : Bounds (387076082889 / 1000000000000) (15524820757 / 40000000000) x267 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx266
  let x268 : ℝ := (2 / 1)*x267
  have hx268 : Bounds (387076082889 / 500000000000) (15524820757 / 20000000000) x268 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx267 <;> norm_num
  let x269 : ℝ := x268*x235
  have hx269 : Bounds (803836892263 / 1000000000000) (806421662179 / 1000000000000) x269 := by
    apply bounds_mul hx268 hx235 <;> norm_num
  let x270 : ℝ := x257+x269
  have hx270 : Bounds (7897923703 / 1000000000000) (23779185619 / 250000000000) x270 := by
    apply bounds_add hx257 hx269 <;> norm_num
  have hPos : 0 < x270 :=
    lt_of_lt_of_le (by norm_num) hx270.1
  have hBridgeL : doubleCapBridgeL x = x48 := by
    exact hEll'
  rw [← doubleCapBridgeDerivativeTraceForm_eq x]
  simpa +zetaDelta only [doubleCapBridgeDerivativeTraceForm,
    hBridgeL, SmallMean.A, biasB, div_one, pow_two] using hPos

theorem acceptedCell : DoubleCapBridgeDerivativeCellCertificate
    (⟨21, by decide⟩ : Fin 256) doubleCapBridgeDerivativeExpression where
  positive x hx := by
    have hloEq : doubleCapBridgeLo (⟨21, by decide⟩ : Fin 256) =
        (1343 / 10240) := by norm_num [doubleCapBridgeLo, doubleCapBridgeStep]
    have hhiEq : doubleCapBridgeHi (⟨21, by decide⟩ : Fin 256) =
        (673 / 5120) := by norm_num [doubleCapBridgeHi, doubleCapBridgeStep]
    have hlo : (1343 / 10240) ≤ x := by
      simpa only [hloEq] using hx.1
    have hhi : x ≤ (673 / 5120) := by
      simpa only [hhiEq] using hx.2
    exact cell_derivative_pos x ⟨hlo, hhi⟩

#print axioms cell_derivative_pos
#print axioms acceptedCell

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell021

end


