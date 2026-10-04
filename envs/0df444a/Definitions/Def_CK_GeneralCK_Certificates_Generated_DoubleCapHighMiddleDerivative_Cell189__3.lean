-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell189__3
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell189__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T15:03:30.164279+00:00
-- url     : https://prove2.me/theorems/73502e47-6490-43b3-a47d-ab53ac652708
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell189 (+2 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell190, Ge…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell189 (+2 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell190, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell191)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell189 (+2 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell190, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell191)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell189 (+2 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell190, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell191) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell189 (+2 modules: GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell190, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell191).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapHighMiddleDerivativeTraceForm
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell189Logs__8

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell189 =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell189
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_derivative_pos (x : ℝ)
    (hx : Bounds (1847 / 10240) (185 / 1024) x) :
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
  have hx0 : Bounds (1847 / 5120) (185 / 512) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx <;> norm_num
  let x1 : ℝ := Real.log (2 / 1)
  have hx1 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x1 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x2 : ℝ := Real.log (2 / 1)
  have hx2 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x2 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x3 : ℝ := (1 / 1)+(185 / 512)
  have hx3 : Bounds (697 / 512) (697 / 512) x3 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((185 / 512) : ℝ)) <;> norm_num
  let x4 : ℝ := (1 / 1)+(185 / 512)
  have hx4 : Bounds (697 / 512) (697 / 512) x4 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((185 / 512) : ℝ)) <;> norm_num
  let x5 : ℝ := Real.log x4
  have hx5 : Bounds (61692157 / 200000000) (154230393 / 500000000) x5 := by
    exact bounds_log hx4 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x6 : ℝ := x3*x5
  have hx6 : Bounds (1312238569 / 3125000000) (209958171721 / 500000000000) x6 := by
    apply bounds_mul hx3 hx5 <;> norm_num
  let x7 : ℝ := -(185 / 512)
  have hx7 : Bounds (-185 / 512) (-185 / 512) x7 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((185 / 512) : ℝ))
  let x8 : ℝ := (1 / 1)+x7
  have hx8 : Bounds (327 / 512) (327 / 512) x8 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx7 <;> norm_num
  let x9 : ℝ := (1 / 1)-(185 / 512)
  have hx9 : Bounds (327 / 512) (327 / 512) x9 := by
    exact hx8
  let x10 : ℝ := -(185 / 512)
  have hx10 : Bounds (-185 / 512) (-185 / 512) x10 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((185 / 512) : ℝ))
  let x11 : ℝ := (1 / 1)+x10
  have hx11 : Bounds (327 / 512) (327 / 512) x11 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx10 <;> norm_num
  let x12 : ℝ := (1 / 1)-(185 / 512)
  have hx12 : Bounds (327 / 512) (327 / 512) x12 := by
    exact hx11
  let x13 : ℝ := Real.log x12
  have hx13 : Bounds (-89672891 / 200000000) (-224182227 / 500000000) x13 := by
    exact bounds_log hx12 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x14 : ℝ := x9*x13
  have hx14 : Bounds (-286357767159 / 1000000000000) (-286357766519 / 1000000000000) x14 := by
    apply bounds_mul hx9 hx13 <;> norm_num
  let x15 : ℝ := x6+x14
  have hx15 : Bounds (133558574921 / 1000000000000) (133558576923 / 1000000000000) x15 := by
    apply bounds_add hx6 hx14 <;> norm_num
  let x16 : ℝ := (2 / 1)⁻¹
  have hx16 : Bounds (1 / 2) (1 / 2) x16 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x17 : ℝ := x15*x16
  have hx17 : Bounds (3338964373 / 50000000000) (33389644231 / 500000000000) x17 := by
    apply bounds_mul hx15 hx16 <;> norm_num
  let x18 : ℝ := x15/(2 / 1)
  have hx18 : Bounds (3338964373 / 50000000000) (33389644231 / 500000000000) x18 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx17
  let x19 : ℝ := -x18
  have hx19 : Bounds (-33389644231 / 500000000000) (-3338964373 / 50000000000) x19 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx18
  let x20 : ℝ := x2+x19
  have hx20 : Bounds (313183945769 / 500000000000) (31318394677 / 50000000000) x20 := by
    apply bounds_add hx2 hx19 <;> norm_num
  let x21 : ℝ := x2-x18
  have hx21 : Bounds (313183945769 / 500000000000) (31318394677 / 50000000000) x21 := by
    exact hx20
  let x22 : ℝ := biasE (185 / 512)
  have hx22 : Bounds (313183945769 / 500000000000) (31318394677 / 50000000000) x22 := by
    simpa +zetaDelta only [biasE, div_one] using hx21
  let x23 : ℝ := Real.log (2 / 1)
  have hx23 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x23 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x24 : ℝ := (1 / 1)+(1847 / 5120)
  have hx24 : Bounds (6967 / 5120) (6967 / 5120) x24 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1847 / 5120) : ℝ)) <;> norm_num
  let x25 : ℝ := (1 / 1)+(1847 / 5120)
  have hx25 : Bounds (6967 / 5120) (6967 / 5120) x25 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1847 / 5120) : ℝ)) <;> norm_num
  let x26 : ℝ := Real.log x25
  have hx26 : Bounds (77007569 / 250000000) (308030277 / 1000000000) x26 := by
    exact bounds_log hx25 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x27 : ℝ := x24*x26
  have hx27 : Bounds (20957489579 / 50000000000) (209574896471 / 500000000000) x27 := by
    apply bounds_mul hx24 hx26 <;> norm_num
  let x28 : ℝ := -(1847 / 5120)
  have hx28 : Bounds (-1847 / 5120) (-1847 / 5120) x28 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1847 / 5120) : ℝ))
  let x29 : ℝ := (1 / 1)+x28
  have hx29 : Bounds (3273 / 5120) (3273 / 5120) x29 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx28 <;> norm_num
  let x30 : ℝ := (1 / 1)-(1847 / 5120)
  have hx30 : Bounds (3273 / 5120) (3273 / 5120) x30 := by
    exact hx29
  let x31 : ℝ := -(1847 / 5120)
  have hx31 : Bounds (-1847 / 5120) (-1847 / 5120) x31 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1847 / 5120) : ℝ))
  let x32 : ℝ := (1 / 1)+x31
  have hx32 : Bounds (3273 / 5120) (3273 / 5120) x32 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx31 <;> norm_num
  let x33 : ℝ := (1 / 1)-(1847 / 5120)
  have hx33 : Bounds (3273 / 5120) (3273 / 5120) x33 := by
    exact hx32
  let x34 : ℝ := Real.log x33
  have hx34 : Bounds (-111861861 / 250000000) (-447447443 / 1000000000) x34 := by
    exact bounds_log hx33 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x35 : ℝ := x30*x34
  have hx35 : Bounds (-286034274261 / 1000000000000) (-14301713681 / 50000000000) x35 := by
    apply bounds_mul hx30 hx34 <;> norm_num
  let x36 : ℝ := x27+x35
  have hx36 : Bounds (133115517319 / 1000000000000) (66557759661 / 500000000000) x36 := by
    apply bounds_add hx27 hx35 <;> norm_num
  let x37 : ℝ := (2 / 1)⁻¹
  have hx37 : Bounds (1 / 2) (1 / 2) x37 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x38 : ℝ := x36*x37
  have hx38 : Bounds (66557758659 / 1000000000000) (66557759661 / 1000000000000) x38 := by
    apply bounds_mul hx36 hx37 <;> norm_num
  let x39 : ℝ := x36/(2 / 1)
  have hx39 : Bounds (66557758659 / 1000000000000) (66557759661 / 1000000000000) x39 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx38
  let x40 : ℝ := -x39
  have hx40 : Bounds (-66557759661 / 1000000000000) (-66557758659 / 1000000000000) x40 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx39
  let x41 : ℝ := x23+x40
  have hx41 : Bounds (626589420339 / 1000000000000) (626589422341 / 1000000000000) x41 := by
    apply bounds_add hx23 hx40 <;> norm_num
  let x42 : ℝ := x23-x39
  have hx42 : Bounds (626589420339 / 1000000000000) (626589422341 / 1000000000000) x42 := by
    exact hx41
  let x43 : ℝ := biasE (1847 / 5120)
  have hx43 : Bounds (626589420339 / 1000000000000) (626589422341 / 1000000000000) x43 := by
    simpa +zetaDelta only [biasE, div_one] using hx42
  let x44 : ℝ := biasE x0
  have hx44 : Bounds (313183945769 / 500000000000) (626589422341 / 1000000000000) x44 := by
    exact bounds_biasE hx0 (by norm_num) (by norm_num) hx22.1 hx43.2
  let x45 : ℝ := x1+x44
  have hx45 : Bounds (659757535769 / 500000000000) (1319736603341 / 1000000000000) x45 := by
    apply bounds_add hx1 hx44 <;> norm_num
  let x46 : ℝ := (2 / 1)⁻¹
  have hx46 : Bounds (1 / 2) (1 / 2) x46 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x47 : ℝ := x45*x46
  have hx47 : Bounds (659757535769 / 1000000000000) (659868301671 / 1000000000000) x47 := by
    apply bounds_mul hx45 hx46 <;> norm_num
  let x48 : ℝ := x45/(2 / 1)
  have hx48 : Bounds (659757535769 / 1000000000000) (659868301671 / 1000000000000) x48 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx47
  let x49 : ℝ := Real.log (2 / 1)
  have hx49 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x49 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x50 : ℝ := (1 / 1)+(128273 / 500000)
  have hx50 : Bounds (628273 / 500000) (628273 / 500000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((128273 / 500000) : ℝ)) <;> norm_num
  let x51 : ℝ := (1 / 1)+(128273 / 500000)
  have hx51 : Bounds (628273 / 500000) (628273 / 500000) x51 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((128273 / 500000) : ℝ)) <;> norm_num
  let x52 : ℝ := Real.log x51
  have hx52 : Bounds (114183343 / 500000000) (228366687 / 1000000000) x52 := by
    exact bounds_log hx51 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x53 : ℝ := x50*x52
  have hx53 : Bounds (143476622913 / 500000000000) (71738311771 / 250000000000) x53 := by
    apply bounds_mul hx50 hx52 <;> norm_num
  let x54 : ℝ := -(128273 / 500000)
  have hx54 : Bounds (-128273 / 500000) (-128273 / 500000) x54 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((128273 / 500000) : ℝ))
  let x55 : ℝ := (1 / 1)+x54
  have hx55 : Bounds (371727 / 500000) (371727 / 500000) x55 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx54 <;> norm_num
  let x56 : ℝ := (1 / 1)-(128273 / 500000)
  have hx56 : Bounds (371727 / 500000) (371727 / 500000) x56 := by
    exact hx55
  let x57 : ℝ := -(128273 / 500000)
  have hx57 : Bounds (-128273 / 500000) (-128273 / 500000) x57 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((128273 / 500000) : ℝ))
  let x58 : ℝ := (1 / 1)+x57
  have hx58 : Bounds (371727 / 500000) (371727 / 500000) x58 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx57 <;> norm_num
  let x59 : ℝ := (1 / 1)-(128273 / 500000)
  have hx59 : Bounds (371727 / 500000) (371727 / 500000) x59 := by
    exact hx58
  let x60 : ℝ := Real.log x59
  have hx60 : Bounds (-59289677 / 200000000) (-2316003 / 7812500) x60 := by
    exact bounds_log hx59 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x61 : ℝ := x56*x60
  have hx61 : Bounds (-110197868811 / 500000000000) (-110197868439 / 500000000000) x61 := by
    apply bounds_mul hx56 hx60 <;> norm_num
  let x62 : ℝ := x53+x61
  have hx62 : Bounds (16639377051 / 250000000000) (33278755103 / 500000000000) x62 := by
    apply bounds_add hx53 hx61 <;> norm_num
  let x63 : ℝ := (2 / 1)⁻¹
  have hx63 : Bounds (1 / 2) (1 / 2) x63 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x64 : ℝ := x62*x63
  have hx64 : Bounds (16639377051 / 500000000000) (33278755103 / 1000000000000) x64 := by
    apply bounds_mul hx62 hx63 <;> norm_num
  let x65 : ℝ := x62/(2 / 1)
  have hx65 : Bounds (16639377051 / 500000000000) (33278755103 / 1000000000000) x65 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx64
  let x66 : ℝ := -x65
  have hx66 : Bounds (-33278755103 / 1000000000000) (-16639377051 / 500000000000) x66 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx65
  let x67 : ℝ := x49+x66
  have hx67 : Bounds (659868424897 / 1000000000000) (329934213449 / 500000000000) x67 := by
    apply bounds_add hx49 hx66 <;> norm_num
  let x68 : ℝ := x49-x65
  have hx68 : Bounds (659868424897 / 1000000000000) (329934213449 / 500000000000) x68 := by
    exact hx67
  let x69 : ℝ := biasE (128273 / 500000)
  have hx69 : Bounds (659868424897 / 1000000000000) (329934213449 / 500000000000) x69 := by
    simpa +zetaDelta only [biasE, div_one] using hx68
  let x70 : ℝ := Real.log (2 / 1)
  have hx70 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x70 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x71 : ℝ := (1 / 1)+(256969 / 1000000)
  have hx71 : Bounds (1256969 / 1000000) (1256969 / 1000000) x71 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((256969 / 1000000) : ℝ)) <;> norm_num
  let x72 : ℝ := (1 / 1)+(256969 / 1000000)
  have hx72 : Bounds (1256969 / 1000000) (1256969 / 1000000) x72 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((256969 / 1000000) : ℝ)) <;> norm_num
  let x73 : ℝ := Real.log x72
  have hx73 : Bounds (228703267 / 1000000000) (57175817 / 250000000) x73 := by
    exact bounds_log hx72 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x74 : ℝ := x71*x73
  have hx74 : Bounds (287472916817 / 1000000000000) (11498916723 / 40000000000) x74 := by
    apply bounds_mul hx71 hx73 <;> norm_num
  let x75 : ℝ := -(256969 / 1000000)
  have hx75 : Bounds (-256969 / 1000000) (-256969 / 1000000) x75 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((256969 / 1000000) : ℝ))
  let x76 : ℝ := (1 / 1)+x75
  have hx76 : Bounds (743031 / 1000000) (743031 / 1000000) x76 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx75 <;> norm_num
  let x77 : ℝ := (1 / 1)-(256969 / 1000000)
  have hx77 : Bounds (743031 / 1000000) (743031 / 1000000) x77 := by
    exact hx76
  let x78 : ℝ := -(256969 / 1000000)
  have hx78 : Bounds (-256969 / 1000000) (-256969 / 1000000) x78 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((256969 / 1000000) : ℝ))
  let x79 : ℝ := (1 / 1)+x78
  have hx79 : Bounds (743031 / 1000000) (743031 / 1000000) x79 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx78 <;> norm_num
  let x80 : ℝ := (1 / 1)-(256969 / 1000000)
  have hx80 : Bounds (743031 / 1000000) (743031 / 1000000) x80 := by
    exact hx79
  let x81 : ℝ := Real.log x80
  have hx81 : Bounds (-297017513 / 1000000000) (-37127189 / 125000000) x81 := by
    exact bounds_log hx80 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x82 : ℝ := x77*x81
  have hx82 : Bounds (-110346609851 / 500000000000) (-110346609479 / 500000000000) x82 := by
    apply bounds_mul hx77 hx81 <;> norm_num
  let x83 : ℝ := x74+x82
  have hx83 : Bounds (13355939423 / 200000000000) (66779699117 / 1000000000000) x83 := by
    apply bounds_add hx74 hx82 <;> norm_num
  let x84 : ℝ := (2 / 1)⁻¹
  have hx84 : Bounds (1 / 2) (1 / 2) x84 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x85 : ℝ := x83*x84
  have hx85 : Bounds (33389848557 / 1000000000000) (33389849559 / 1000000000000) x85 := by
    apply bounds_mul hx83 hx84 <;> norm_num
  let x86 : ℝ := x83/(2 / 1)
  have hx86 : Bounds (33389848557 / 1000000000000) (33389849559 / 1000000000000) x86 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx85
  let x87 : ℝ := -x86
  have hx87 : Bounds (-33389849559 / 1000000000000) (-33389848557 / 1000000000000) x87 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx86
  let x88 : ℝ := x70+x87
  have hx88 : Bounds (659757330441 / 1000000000000) (659757332443 / 1000000000000) x88 := by
    apply bounds_add hx70 hx87 <;> norm_num
  let x89 : ℝ := x70-x86
  have hx89 : Bounds (659757330441 / 1000000000000) (659757332443 / 1000000000000) x89 := by
    exact hx88
  let x90 : ℝ := biasE (256969 / 1000000)
  have hx90 : Bounds (659757330441 / 1000000000000) (659757332443 / 1000000000000) x90 := by
    simpa +zetaDelta only [biasE, div_one] using hx89
  let y : ℝ := doubleCapHighTailY x
  have hEll' : Real.log 2 * doubleCapHighTailFloor x = x48 := by
    simpa +zetaDelta only [div_one] using hEll
  have hy : Bounds (128273 / 500000) (256969 / 1000000) y := by
    dsimp only [y, doubleCapHighTailY]
    apply entropyInverseBias_bracket hh0.le hh1.le
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (256969 / 1000000) ≤ (659757332443 / 1000000000000) := hx90.2
      have h2 : (659757535769 / 1000000000000) ≤ x48 := hx48.1
      linarith [hEll']
    · have h1 : x48 ≤ (659868301671 / 1000000000000) := hx48.2
      have h2 : (659868424897 / 1000000000000) ≤ biasE (128273 / 500000) := hx69.1
      linarith [hEll']
  let x91 : ℝ := x⁻¹
  have hx91 : Bounds (1107027027027 / 200000000000) (693015701137 / 125000000000) x91 := by
    apply bounds_inv hx <;> norm_num
  let x92 : ℝ := x48*x91
  have hx92 : Bounds (730369423381 / 200000000000) (146335709997 / 40000000000) x92 := by
    apply bounds_mul hx48 hx91 <;> norm_num
  let x93 : ℝ := x48/x
  have hx93 : Bounds (730369423381 / 200000000000) (146335709997 / 40000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(92387 / 500000)
  have hx95 : Bounds (592387 / 500000) (592387 / 500000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((92387 / 500000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(92387 / 500000)
  have hx96 : Bounds (592387 / 500000) (592387 / 500000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((92387 / 500000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (169552039 / 1000000000) (4238801 / 25000000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (100440423727 / 500000000000) (200880848639 / 1000000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(92387 / 500000)
  have hx99 : Bounds (-92387 / 500000) (-92387 / 500000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((92387 / 500000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (407613 / 500000) (407613 / 500000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(92387 / 500000)
  have hx101 : Bounds (407613 / 500000) (407613 / 500000) x101 := by
    exact hx100
  let x102 : ℝ := -(92387 / 500000)
  have hx102 : Bounds (-92387 / 500000) (-92387 / 500000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((92387 / 500000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (407613 / 500000) (407613 / 500000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(92387 / 500000)
  have hx104 : Bounds (407613 / 500000) (407613 / 500000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-12768119 / 62500000) (-204289903 / 1000000000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-166542441279 / 1000000000000) (-166542440463 / 1000000000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (1373536247 / 40000000000) (2146150511 / 62500000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (17169203087 / 1000000000000) (2146150511 / 125000000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (17169203087 / 1000000000000) (2146150511 / 125000000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-2146150511 / 125000000000) (-17169203087 / 1000000000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (84497246989 / 125000000000) (675977977913 / 1000000000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (84497246989 / 125000000000) (675977977913 / 1000000000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (92387 / 500000)
  have hx114 : Bounds (84497246989 / 125000000000) (675977977913 / 1000000000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(18509 / 100000)
  have hx116 : Bounds (118509 / 100000) (118509 / 100000) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((18509 / 100000) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(18509 / 100000)
  have hx117 : Bounds (118509 / 100000) (118509 / 100000) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((18509 / 100000) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (169818721 / 1000000000) (84909361 / 500000000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (201250468069 / 1000000000000) (40250093851 / 200000000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(18509 / 100000)
  have hx120 : Bounds (-18509 / 100000) (-18509 / 100000) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((18509 / 100000) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (81491 / 100000) (81491 / 100000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(18509 / 100000)
  have hx122 : Bounds (81491 / 100000) (81491 / 100000) x122 := by
    exact hx121
  let x123 : ℝ := -(18509 / 100000)
  have hx123 : Bounds (-18509 / 100000) (-18509 / 100000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((18509 / 100000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (81491 / 100000) (81491 / 100000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(18509 / 100000)
  have hx125 : Bounds (81491 / 100000) (81491 / 100000) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-102338801 / 500000000) (-204677601 / 1000000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-83396912323 / 500000000000) (-16679382383 / 100000000000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (34456643423 / 1000000000000) (1378265817 / 40000000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (17228321711 / 1000000000000) (17228322713 / 1000000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (17228321711 / 1000000000000) (17228322713 / 1000000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-17228322713 / 1000000000000) (-17228321711 / 1000000000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (675918857287 / 1000000000000) (675918859289 / 1000000000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (675918857287 / 1000000000000) (675918859289 / 1000000000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (18509 / 100000)
  have hx135 : Bounds (675918857287 / 1000000000000) (675918859289 / 1000000000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(92387 / 500000)
  have hx136 : Bounds (674766399179 / 1000000000000) (27039034479 / 40000000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((92387 / 500000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(18509 / 100000)
  have hx137 : Bounds (675920382867 / 1000000000000) (169282978521 / 250000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((18509 / 100000) : ℝ)) <;> norm_num
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
  have hc : Bounds (92387 / 500000) (18509 / 100000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num)
      (by norm_num) (show 0 < x93 by linarith [hx93.1]) hcEq
    · have h1 : x93 * (92387 / 500000) ≤ (27039034479 / 40000000000) := hx136.2
      have h2 : (84497246989 / 125000000000) ≤ biasE (92387 / 500000) := hx114.1
      linarith
    · have h1 : biasE (18509 / 100000) ≤ (675918859289 / 1000000000000) := hx135.2
      have h2 : (675920382867 / 1000000000000) ≤ x93 * (18509 / 100000) := hx137.1
      linarith
  let x138 : ℝ := (1 / 1)+x0
  have hx138 : Bounds (6967 / 5120) (697 / 512) x138 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx0 <;> norm_num
  let x139 : ℝ := -x0
  have hx139 : Bounds (-185 / 512) (-1847 / 5120) x139 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x140 : ℝ := (1 / 1)+x139
  have hx140 : Bounds (327 / 512) (3273 / 5120) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx139 <;> norm_num
  let x141 : ℝ := (1 / 1)-x0
  have hx141 : Bounds (327 / 512) (3273 / 5120) x141 := by
    exact hx140
  let x142 : ℝ := x141⁻¹
  have hx142 : Bounds (1564314084937 / 1000000000000) (62629969419 / 40000000000) x142 := by
    apply bounds_inv hx141 <;> norm_num
  let x143 : ℝ := x138*x142
  have hx143 : Bounds (1064314084937 / 500000000000) (42629969419 / 20000000000) x143 := by
    apply bounds_mul hx138 hx142 <;> norm_num
  let x144 : ℝ := x138/x141
  have hx144 : Bounds (1064314084937 / 500000000000) (42629969419 / 20000000000) x144 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx143
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (755477719 / 1000000000) (756825241 / 1000000000) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_14.2)
  let x146 : ℝ := (2 / 1)⁻¹
  have hx146 : Bounds (1 / 2) (1 / 2) x146 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x147 : ℝ := x145*x146
  have hx147 : Bounds (755477719 / 2000000000) (756825241 / 2000000000) x147 := by
    apply bounds_mul hx145 hx146 <;> norm_num
  let x148 : ℝ := x145/(2 / 1)
  have hx148 : Bounds (755477719 / 2000000000) (756825241 / 2000000000) x148 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx147
  let x149 : ℝ := (1 / 1)+y
  have hx149 : Bounds (628273 / 500000) (1256969 / 1000000) x149 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x150 : ℝ := -y
  have hx150 : Bounds (-256969 / 1000000) (-128273 / 500000) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (743031 / 1000000) (371727 / 500000) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-y
  have hx152 : Bounds (743031 / 1000000) (371727 / 500000) x152 := by
    exact hx151
  let x153 : ℝ := x152⁻¹
  have hx153 : Bounds (672536565813 / 500000000000) (10514366157 / 7812500000) x153 := by
    apply bounds_inv hx152 <;> norm_num
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (422536565813 / 250000000000) (6608116157 / 3906250000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x149/x152
  have hx155 : Bounds (422536565813 / 250000000000) (6608116157 / 3906250000) x155 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx154
  let x156 : ℝ := Real.log x155
  have hx156 : Bounds (524815071 / 1000000000) (26286039 / 50000000) x156 := by
    exact bounds_log hx155 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_16.2)
  let x157 : ℝ := (2 / 1)⁻¹
  have hx157 : Bounds (1 / 2) (1 / 2) x157 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x158 : ℝ := x156*x157
  have hx158 : Bounds (524815071 / 2000000000) (26286039 / 100000000) x158 := by
    apply bounds_mul hx156 hx157 <;> norm_num
  let x159 : ℝ := x156/(2 / 1)
  have hx159 : Bounds (524815071 / 2000000000) (26286039 / 100000000) x159 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx158
  let x160 : ℝ := (1 / 1)+c
  have hx160 : Bounds (592387 / 500000) (118509 / 100000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x161 : ℝ := -c
  have hx161 : Bounds (-18509 / 100000) (-92387 / 500000) x161 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x162 : ℝ := (1 / 1)+x161
  have hx162 : Bounds (81491 / 100000) (407613 / 500000) x162 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx161 <;> norm_num
  let x163 : ℝ := (1 / 1)-c
  have hx163 : Bounds (81491 / 100000) (407613 / 500000) x163 := by
    exact hx162
  let x164 : ℝ := x163⁻¹
  have hx164 : Bounds (1226653713203 / 1000000000000) (1227129376251 / 1000000000000) x164 := by
    apply bounds_inv hx163 <;> norm_num
  let x165 : ℝ := x160*x164
  have hx165 : Bounds (726653713203 / 500000000000) (727129376251 / 500000000000) x165 := by
    apply bounds_mul hx160 hx164 <;> norm_num
  let x166 : ℝ := x160/x163
  have hx166 : Bounds (726653713203 / 500000000000) (727129376251 / 500000000000) x166 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx165
  let x167 : ℝ := Real.log x166
  have hx167 : Bounds (186920971 / 500000000) (374496323 / 1000000000) x167 := by
    exact bounds_log hx166 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x168 : ℝ := (2 / 1)⁻¹
  have hx168 : Bounds (1 / 2) (1 / 2) x168 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x169 : ℝ := x167*x168
  have hx169 : Bounds (186920971 / 1000000000) (374496323 / 2000000000) x169 := by
    apply bounds_mul hx167 hx168 <;> norm_num
  let x170 : ℝ := x167/(2 / 1)
  have hx170 : Bounds (186920971 / 1000000000) (374496323 / 2000000000) x170 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx169
  let x171 : ℝ := Real.log (2 / 1)
  have hx171 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x171 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x172 : ℝ := c*c
  have hx172 : Bounds (8535357769 / 250000000000) (342583081 / 10000000000) x172 := by
    apply bounds_mul hc hc <;> norm_num
  let x173 : ℝ := -x172
  have hx173 : Bounds (-342583081 / 10000000000) (-8535357769 / 250000000000) x173 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx172
  let x174 : ℝ := (1 / 1)+x173
  have hx174 : Bounds (9657416919 / 10000000000) (241464642231 / 250000000000) x174 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx173 <;> norm_num
  let x175 : ℝ := (1 / 1)-x172
  have hx175 : Bounds (9657416919 / 10000000000) (241464642231 / 250000000000) x175 := by
    exact hx174
  let x176 : ℝ := Real.log x175
  have hx176 : Bounds (-34858881 / 1000000000) (-4342233 / 125000000) x176 := by
    exact bounds_log hx175 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (-34858881 / 2000000000) (-4342233 / 250000000) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (-34858881 / 2000000000) (-4342233 / 250000000) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (4342233 / 250000000) (34858881 / 2000000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x171+x180
  have hx181 : Bounds (44407257 / 62500000) (1421153243 / 2000000000) x181 := by
    apply bounds_add hx171 hx180 <;> norm_num
  let x182 : ℝ := x171-x179
  have hx182 : Bounds (44407257 / 62500000) (1421153243 / 2000000000) x182 := by
    exact hx181
  let x183 : ℝ := Real.log (2 / 1)
  have hx183 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x183 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x184 : ℝ := (1 / 1)+(18509 / 100000)
  have hx184 : Bounds (118509 / 100000) (118509 / 100000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((18509 / 100000) : ℝ)) <;> norm_num
  let x185 : ℝ := (1 / 1)+(18509 / 100000)
  have hx185 : Bounds (118509 / 100000) (118509 / 100000) x185 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((18509 / 100000) : ℝ)) <;> norm_num
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (169818721 / 1000000000) (84909361 / 500000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x187 : ℝ := x184*x186
  have hx187 : Bounds (201250468069 / 1000000000000) (40250093851 / 200000000000) x187 := by
    apply bounds_mul hx184 hx186 <;> norm_num
  let x188 : ℝ := -(18509 / 100000)
  have hx188 : Bounds (-18509 / 100000) (-18509 / 100000) x188 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((18509 / 100000) : ℝ))
  let x189 : ℝ := (1 / 1)+x188
  have hx189 : Bounds (81491 / 100000) (81491 / 100000) x189 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx188 <;> norm_num
  let x190 : ℝ := (1 / 1)-(18509 / 100000)
  have hx190 : Bounds (81491 / 100000) (81491 / 100000) x190 := by
    exact hx189
  let x191 : ℝ := -(18509 / 100000)
  have hx191 : Bounds (-18509 / 100000) (-18509 / 100000) x191 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((18509 / 100000) : ℝ))
  let x192 : ℝ := (1 / 1)+x191
  have hx192 : Bounds (81491 / 100000) (81491 / 100000) x192 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx191 <;> norm_num
  let x193 : ℝ := (1 / 1)-(18509 / 100000)
  have hx193 : Bounds (81491 / 100000) (81491 / 100000) x193 := by
    exact hx192
  let x194 : ℝ := Real.log x193
  have hx194 : Bounds (-102338801 / 500000000) (-204677601 / 1000000000) x194 := by
    exact bounds_log hx193 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x195 : ℝ := x190*x194
  have hx195 : Bounds (-83396912323 / 500000000000) (-16679382383 / 100000000000) x195 := by
    apply bounds_mul hx190 hx194 <;> norm_num
  let x196 : ℝ := x187+x195
  have hx196 : Bounds (34456643423 / 1000000000000) (1378265817 / 40000000000) x196 := by
    apply bounds_add hx187 hx195 <;> norm_num
  let x197 : ℝ := (2 / 1)⁻¹
  have hx197 : Bounds (1 / 2) (1 / 2) x197 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x198 : ℝ := x196*x197
  have hx198 : Bounds (17228321711 / 1000000000000) (17228322713 / 1000000000000) x198 := by
    apply bounds_mul hx196 hx197 <;> norm_num
  let x199 : ℝ := x196/(2 / 1)
  have hx199 : Bounds (17228321711 / 1000000000000) (17228322713 / 1000000000000) x199 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx198
  let x200 : ℝ := -x199
  have hx200 : Bounds (-17228322713 / 1000000000000) (-17228321711 / 1000000000000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx199
  let x201 : ℝ := x183+x200
  have hx201 : Bounds (675918857287 / 1000000000000) (675918859289 / 1000000000000) x201 := by
    apply bounds_add hx183 hx200 <;> norm_num
  let x202 : ℝ := x183-x199
  have hx202 : Bounds (675918857287 / 1000000000000) (675918859289 / 1000000000000) x202 := by
    exact hx201
  let x203 : ℝ := biasE (18509 / 100000)
  have hx203 : Bounds (675918857287 / 1000000000000) (675918859289 / 1000000000000) x203 := by
    simpa +zetaDelta only [biasE, div_one] using hx202
  let x204 : ℝ := Real.log (2 / 1)
  have hx204 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x204 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x205 : ℝ := (1 / 1)+(92387 / 500000)
  have hx205 : Bounds (592387 / 500000) (592387 / 500000) x205 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((92387 / 500000) : ℝ)) <;> norm_num
  let x206 : ℝ := (1 / 1)+(92387 / 500000)
  have hx206 : Bounds (592387 / 500000) (592387 / 500000) x206 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((92387 / 500000) : ℝ)) <;> norm_num
  let x207 : ℝ := Real.log x206
  have hx207 : Bounds (169552039 / 1000000000) (4238801 / 25000000) x207 := by
    exact bounds_log hx206 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x208 : ℝ := x205*x207
  have hx208 : Bounds (100440423727 / 500000000000) (200880848639 / 1000000000000) x208 := by
    apply bounds_mul hx205 hx207 <;> norm_num
  let x209 : ℝ := -(92387 / 500000)
  have hx209 : Bounds (-92387 / 500000) (-92387 / 500000) x209 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((92387 / 500000) : ℝ))
  let x210 : ℝ := (1 / 1)+x209
  have hx210 : Bounds (407613 / 500000) (407613 / 500000) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx209 <;> norm_num
  let x211 : ℝ := (1 / 1)-(92387 / 500000)
  have hx211 : Bounds (407613 / 500000) (407613 / 500000) x211 := by
    exact hx210
  let x212 : ℝ := -(92387 / 500000)
  have hx212 : Bounds (-92387 / 500000) (-92387 / 500000) x212 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((92387 / 500000) : ℝ))
  let x213 : ℝ := (1 / 1)+x212
  have hx213 : Bounds (407613 / 500000) (407613 / 500000) x213 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx212 <;> norm_num
  let x214 : ℝ := (1 / 1)-(92387 / 500000)
  have hx214 : Bounds (407613 / 500000) (407613 / 500000) x214 := by
    exact hx213
  let x215 : ℝ := Real.log x214
  have hx215 : Bounds (-12768119 / 62500000) (-204289903 / 1000000000) x215 := by
    exact bounds_log hx214 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x216 : ℝ := x211*x215
  have hx216 : Bounds (-166542441279 / 1000000000000) (-166542440463 / 1000000000000) x216 := by
    apply bounds_mul hx211 hx215 <;> norm_num
  let x217 : ℝ := x208+x216
  have hx217 : Bounds (1373536247 / 40000000000) (2146150511 / 62500000000) x217 := by
    apply bounds_add hx208 hx216 <;> norm_num
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (17169203087 / 1000000000000) (2146150511 / 125000000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (17169203087 / 1000000000000) (2146150511 / 125000000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := -x220
  have hx221 : Bounds (-2146150511 / 125000000000) (-17169203087 / 1000000000000) x221 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx220
  let x222 : ℝ := x204+x221
  have hx222 : Bounds (84497246989 / 125000000000) (675977977913 / 1000000000000) x222 := by
    apply bounds_add hx204 hx221 <;> norm_num
  let x223 : ℝ := x204-x220
  have hx223 : Bounds (84497246989 / 125000000000) (675977977913 / 1000000000000) x223 := by
    exact hx222
  let x224 : ℝ := biasE (92387 / 500000)
  have hx224 : Bounds (84497246989 / 125000000000) (675977977913 / 1000000000000) x224 := by
    simpa +zetaDelta only [biasE, div_one] using hx223
  let x225 : ℝ := biasE c
  have hx225 : Bounds (675918857287 / 1000000000000) (675977977913 / 1000000000000) x225 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx203.1 hx224.2
  let x226 : ℝ := x159⁻¹
  have hx226 : Bounds (1902150415283 / 500000000000) (3810866170801 / 1000000000000) x226 := by
    apply bounds_inv hx159 <;> norm_num
  let x227 : ℝ := x148*x226
  have hx227 : Bounds (359258064233 / 250000000000) (360519963517 / 250000000000) x227 := by
    apply bounds_mul hx148 hx226 <;> norm_num
  let x228 : ℝ := x148/x159
  have hx228 : Bounds (359258064233 / 250000000000) (360519963517 / 250000000000) x228 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx227
  let x229 : ℝ := c*x148
  have hx229 : Bounds (2791852801 / 40000000000) (70040391929 / 1000000000000) x229 := by
    apply bounds_mul hc hx148 <;> norm_num
  let x230 : ℝ := x225+x229
  have hx230 : Bounds (23303599291 / 31250000000) (373009184921 / 500000000000) x230 := by
    apply bounds_add hx225 hx229 <;> norm_num
  let x231 : ℝ := x*x170
  have hx231 : Bounds (2107196249 / 62500000000) (33829013553 / 1000000000000) x231 := by
    apply bounds_mul hx hx170 <;> norm_num
  let x232 : ℝ := x48+x231
  have hx232 : Bounds (693472675753 / 1000000000000) (86712164403 / 125000000000) x232 := by
    apply bounds_add hx48 hx231 <;> norm_num
  let x233 : ℝ := x232⁻¹
  have hx233 : Bounds (1441550915729 / 1000000000000) (721008941639 / 500000000000) x233 := by
    apply bounds_inv hx232 <;> norm_num
  let x234 : ℝ := x230*x233
  have hx234 : Bounds (1074986396727 / 1000000000000) (1075771830567 / 1000000000000) x234 := by
    apply bounds_mul hx230 hx233 <;> norm_num
  let x235 : ℝ := x230/x232
  have hx235 : Bounds (1074986396727 / 1000000000000) (1075771830567 / 1000000000000) x235 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx234
  let x236 : ℝ := y*y
  have hx236 : Bounds (16453962529 / 250000000000) (66033066961 / 1000000000000) x236 := by
    apply bounds_mul hy hy <;> norm_num
  let x237 : ℝ := -x236
  have hx237 : Bounds (-66033066961 / 1000000000000) (-16453962529 / 250000000000) x237 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx236
  let x238 : ℝ := (1 / 1)+x237
  have hx238 : Bounds (933966933039 / 1000000000000) (233546037471 / 250000000000) x238 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx237 <;> norm_num
  let x239 : ℝ := (1 / 1)-x236
  have hx239 : Bounds (933966933039 / 1000000000000) (233546037471 / 250000000000) x239 := by
    exact hx238
  let x240 : ℝ := x239*x159
  have hx240 : Bounds (245079961137 / 1000000000000) (245560009971 / 1000000000000) x240 := by
    apply bounds_mul hx239 hx159 <;> norm_num
  let x241 : ℝ := c*c
  have hx241 : Bounds (8535357769 / 250000000000) (342583081 / 10000000000) x241 := by
    apply bounds_mul hc hc <;> norm_num
  let x242 : ℝ := -x241
  have hx242 : Bounds (-342583081 / 10000000000) (-8535357769 / 250000000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx241
  let x243 : ℝ := (1 / 1)+x242
  have hx243 : Bounds (9657416919 / 10000000000) (241464642231 / 250000000000) x243 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx242 <;> norm_num
  let x244 : ℝ := (1 / 1)-x241
  have hx244 : Bounds (9657416919 / 10000000000) (241464642231 / 250000000000) x244 := by
    exact hx243
  let x245 : ℝ := x244*x182
  have hx245 : Bounds (5489400257 / 8000000000) (686316518753 / 1000000000000) x245 := by
    apply bounds_mul hx244 hx182 <;> norm_num
  let x246 : ℝ := y*y
  have hx246 : Bounds (16453962529 / 250000000000) (66033066961 / 1000000000000) x246 := by
    apply bounds_mul hy hy <;> norm_num
  let x247 : ℝ := (1 / 1)+x246
  have hx247 : Bounds (266453962529 / 250000000000) (1066033066961 / 1000000000000) x247 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx246 <;> norm_num
  let x248 : ℝ := x247*x159
  have hx248 : Bounds (11187124421 / 40000000000) (56043573547 / 200000000000) x248 := by
    apply bounds_mul hx247 hx159 <;> norm_num
  let x249 : ℝ := -y
  have hx249 : Bounds (-256969 / 1000000) (-128273 / 500000) x249 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x250 : ℝ := x248+x249
  have hx250 : Bounds (908364421 / 40000000000) (4734373547 / 200000000000) x250 := by
    apply bounds_add hx248 hx249 <;> norm_num
  let x251 : ℝ := x248-y
  have hx251 : Bounds (908364421 / 40000000000) (4734373547 / 200000000000) x251 := by
    exact hx250
  let x252 : ℝ := x240*x240
  have hx252 : Bounds (1201283747 / 20000000000) (60299718497 / 1000000000000) x252 := by
    apply bounds_mul hx240 hx240 <;> norm_num
  let x253 : ℝ := x252⁻¹
  have hx253 : Bounds (16583825346543 / 1000000000000) (16648855900987 / 1000000000000) x253 := by
    apply bounds_inv hx252 <;> norm_num
  let x254 : ℝ := x251*x253
  have hx254 : Bounds (376603922721 / 1000000000000) (98527378707 / 250000000000) x254 := by
    apply bounds_mul hx251 hx253 <;> norm_num
  let x255 : ℝ := x251/x252
  have hx255 : Bounds (376603922721 / 1000000000000) (98527378707 / 250000000000) x255 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx254
  let x256 : ℝ := (-2 / 1)*x255
  have hx256 : Bounds (-98527378707 / 125000000000) (-376603922721 / 500000000000) x256 := by
    apply bounds_mul (bounds_const ((-2 / 1) : ℝ)) hx255 <;> norm_num
  let x257 : ℝ := x256*x228
  have hx257 : Bounds (-56833739163 / 50000000000) (-541191985037 / 500000000000) x257 := by
    apply bounds_mul hx256 hx228 <;> norm_num
  let x258 : ℝ := (2 / 1)*x182
  have hx258 : Bounds (44407257 / 31250000) (1421153243 / 1000000000) x258 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx182 <;> norm_num
  let x259 : ℝ := c*c
  have hx259 : Bounds (8535357769 / 250000000000) (342583081 / 10000000000) x259 := by
    apply bounds_mul hc hc <;> norm_num
  let x260 : ℝ := -x259
  have hx260 : Bounds (-342583081 / 10000000000) (-8535357769 / 250000000000) x260 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx259
  let x261 : ℝ := x258+x260
  have hx261 : Bounds (13867739159 / 10000000000) (346752952981 / 250000000000) x261 := by
    apply bounds_add hx258 hx260 <;> norm_num
  let x262 : ℝ := x258-x259
  have hx262 : Bounds (13867739159 / 10000000000) (346752952981 / 250000000000) x262 := by
    exact hx261
  let x263 : ℝ := c*x262
  have hx263 : Bounds (16014985221 / 62500000000) (25672201627 / 100000000000) x263 := by
    apply bounds_mul hc hx262 <;> norm_num
  let x264 : ℝ := x245*x245
  have hx264 : Bounds (470836174711 / 1000000000000) (235515181957 / 500000000000) x264 := by
    apply bounds_mul hx245 hx245 <;> norm_num
  let x265 : ℝ := x264⁻¹
  have hx265 : Bounds (265375673367 / 125000000000) (1061940494073 / 500000000000) x265 := by
    apply bounds_inv hx264 <;> norm_num
  let x266 : ℝ := x263*x265
  have hx266 : Bounds (271999199167 / 500000000000) (109049401919 / 200000000000) x266 := by
    apply bounds_mul hx263 hx265 <;> norm_num
  let x267 : ℝ := x263/x264
  have hx267 : Bounds (271999199167 / 500000000000) (109049401919 / 200000000000) x267 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx266
  let x268 : ℝ := (2 / 1)*x267
  have hx268 : Bounds (271999199167 / 250000000000) (109049401919 / 100000000000) x268 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx267 <;> norm_num
  let x269 : ℝ := x268*x235
  have hx269 : Bounds (11695817561 / 10000000000) (1173122747247 / 1000000000000) x269 := by
    apply bounds_mul hx268 hx235 <;> norm_num
  let x270 : ℝ := x257+x269
  have hx270 : Bounds (822674321 / 25000000000) (90738777173 / 1000000000000) x270 := by
    apply bounds_add hx257 hx269 <;> norm_num
  have hPos : 0 < x270 :=
    lt_of_lt_of_le (by norm_num) hx270.1
  have hBridgeL : doubleCapBridgeL x = x48 := by
    exact hEll'
  rw [← doubleCapBridgeDerivativeTraceForm_eq x]
  simpa +zetaDelta only [doubleCapBridgeDerivativeTraceForm,
    hBridgeL, SmallMean.A, biasB, div_one, pow_two] using hPos

theorem acceptedCell : DoubleCapBridgeDerivativeCellCertificate
    (⟨189, by decide⟩ : Fin 256) doubleCapBridgeDerivativeExpression where
  positive x hx := by
    have hloEq : doubleCapBridgeLo (⟨189, by decide⟩ : Fin 256) =
        (1847 / 10240) := by norm_num [doubleCapBridgeLo, doubleCapBridgeStep]
    have hhiEq : doubleCapBridgeHi (⟨189, by decide⟩ : Fin 256) =
        (185 / 1024) := by norm_num [doubleCapBridgeHi, doubleCapBridgeStep]
    have hlo : (1847 / 10240) ≤ x := by
      simpa only [hloEq] using hx.1
    have hhi : x ≤ (185 / 1024) := by
      simpa only [hhiEq] using hx.2
    exact cell_derivative_pos x ⟨hlo, hhi⟩

#print axioms cell_derivative_pos
#print axioms acceptedCell

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell189

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell190 =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell190
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_derivative_pos (x : ℝ)
    (hx : Bounds (185 / 1024) (1853 / 10240) x) :
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
  have hx0 : Bounds (185 / 512) (1853 / 5120) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx <;> norm_num
  let x1 : ℝ := Real.log (2 / 1)
  have hx1 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x1 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x2 : ℝ := Real.log (2 / 1)
  have hx2 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x2 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x3 : ℝ := (1 / 1)+(1853 / 5120)
  have hx3 : Bounds (6973 / 5120) (6973 / 5120) x3 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1853 / 5120) : ℝ)) <;> norm_num
  let x4 : ℝ := (1 / 1)+(1853 / 5120)
  have hx4 : Bounds (6973 / 5120) (6973 / 5120) x4 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1853 / 5120) : ℝ)) <;> norm_num
  let x5 : ℝ := Real.log x4
  have hx5 : Bounds (308891109 / 1000000000) (30889111 / 100000000) x5 := by
    exact bounds_log hx4 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x6 : ℝ := x3*x5
  have hx6 : Bounds (52585393141 / 125000000000) (420683146491 / 1000000000000) x6 := by
    apply bounds_mul hx3 hx5 <;> norm_num
  let x7 : ℝ := -(1853 / 5120)
  have hx7 : Bounds (-1853 / 5120) (-1853 / 5120) x7 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1853 / 5120) : ℝ))
  let x8 : ℝ := (1 / 1)+x7
  have hx8 : Bounds (3267 / 5120) (3267 / 5120) x8 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx7 <;> norm_num
  let x9 : ℝ := (1 / 1)-(1853 / 5120)
  have hx9 : Bounds (3267 / 5120) (3267 / 5120) x9 := by
    exact hx8
  let x10 : ℝ := -(1853 / 5120)
  have hx10 : Bounds (-1853 / 5120) (-1853 / 5120) x10 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1853 / 5120) : ℝ))
  let x11 : ℝ := (1 / 1)+x10
  have hx11 : Bounds (3267 / 5120) (3267 / 5120) x11 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx10 <;> norm_num
  let x12 : ℝ := (1 / 1)-(1853 / 5120)
  have hx12 : Bounds (3267 / 5120) (3267 / 5120) x12 := by
    exact hx11
  let x13 : ℝ := Real.log x12
  have hx13 : Bounds (-449282307 / 1000000000) (-224641153 / 500000000) x13 := by
    exact bounds_log hx12 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x14 : ℝ := x9*x13
  have hx14 : Bounds (-57336144413 / 200000000000) (-143340360713 / 500000000000) x14 := by
    apply bounds_mul hx9 hx13 <;> norm_num
  let x15 : ℝ := x6+x14
  have hx15 : Bounds (134002423063 / 1000000000000) (26800485013 / 200000000000) x15 := by
    apply bounds_add hx6 hx14 <;> norm_num
  let x16 : ℝ := (2 / 1)⁻¹
  have hx16 : Bounds (1 / 2) (1 / 2) x16 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x17 : ℝ := x15*x16
  have hx17 : Bounds (67001211531 / 1000000000000) (67001212533 / 1000000000000) x17 := by
    apply bounds_mul hx15 hx16 <;> norm_num
  let x18 : ℝ := x15/(2 / 1)
  have hx18 : Bounds (67001211531 / 1000000000000) (67001212533 / 1000000000000) x18 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx17
  let x19 : ℝ := -x18
  have hx19 : Bounds (-67001212533 / 1000000000000) (-67001211531 / 1000000000000) x19 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx18
  let x20 : ℝ := x2+x19
  have hx20 : Bounds (626145967467 / 1000000000000) (626145969469 / 1000000000000) x20 := by
    apply bounds_add hx2 hx19 <;> norm_num
  let x21 : ℝ := x2-x18
  have hx21 : Bounds (626145967467 / 1000000000000) (626145969469 / 1000000000000) x21 := by
    exact hx20
  let x22 : ℝ := biasE (1853 / 5120)
  have hx22 : Bounds (626145967467 / 1000000000000) (626145969469 / 1000000000000) x22 := by
    simpa +zetaDelta only [biasE, div_one] using hx21
  let x23 : ℝ := Real.log (2 / 1)
  have hx23 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x23 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x24 : ℝ := (1 / 1)+(185 / 512)
  have hx24 : Bounds (697 / 512) (697 / 512) x24 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((185 / 512) : ℝ)) <;> norm_num
  let x25 : ℝ := (1 / 1)+(185 / 512)
  have hx25 : Bounds (697 / 512) (697 / 512) x25 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((185 / 512) : ℝ)) <;> norm_num
  let x26 : ℝ := Real.log x25
  have hx26 : Bounds (61692157 / 200000000) (154230393 / 500000000) x26 := by
    exact bounds_log hx25 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x27 : ℝ := x24*x26
  have hx27 : Bounds (1312238569 / 3125000000) (209958171721 / 500000000000) x27 := by
    apply bounds_mul hx24 hx26 <;> norm_num
  let x28 : ℝ := -(185 / 512)
  have hx28 : Bounds (-185 / 512) (-185 / 512) x28 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((185 / 512) : ℝ))
  let x29 : ℝ := (1 / 1)+x28
  have hx29 : Bounds (327 / 512) (327 / 512) x29 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx28 <;> norm_num
  let x30 : ℝ := (1 / 1)-(185 / 512)
  have hx30 : Bounds (327 / 512) (327 / 512) x30 := by
    exact hx29
  let x31 : ℝ := -(185 / 512)
  have hx31 : Bounds (-185 / 512) (-185 / 512) x31 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((185 / 512) : ℝ))
  let x32 : ℝ := (1 / 1)+x31
  have hx32 : Bounds (327 / 512) (327 / 512) x32 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx31 <;> norm_num
  let x33 : ℝ := (1 / 1)-(185 / 512)
  have hx33 : Bounds (327 / 512) (327 / 512) x33 := by
    exact hx32
  let x34 : ℝ := Real.log x33
  have hx34 : Bounds (-89672891 / 200000000) (-224182227 / 500000000) x34 := by
    exact bounds_log hx33 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x35 : ℝ := x30*x34
  have hx35 : Bounds (-286357767159 / 1000000000000) (-286357766519 / 1000000000000) x35 := by
    apply bounds_mul hx30 hx34 <;> norm_num
  let x36 : ℝ := x27+x35
  have hx36 : Bounds (133558574921 / 1000000000000) (133558576923 / 1000000000000) x36 := by
    apply bounds_add hx27 hx35 <;> norm_num
  let x37 : ℝ := (2 / 1)⁻¹
  have hx37 : Bounds (1 / 2) (1 / 2) x37 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x38 : ℝ := x36*x37
  have hx38 : Bounds (3338964373 / 50000000000) (33389644231 / 500000000000) x38 := by
    apply bounds_mul hx36 hx37 <;> norm_num
  let x39 : ℝ := x36/(2 / 1)
  have hx39 : Bounds (3338964373 / 50000000000) (33389644231 / 500000000000) x39 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx38
  let x40 : ℝ := -x39
  have hx40 : Bounds (-33389644231 / 500000000000) (-3338964373 / 50000000000) x40 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx39
  let x41 : ℝ := x23+x40
  have hx41 : Bounds (313183945769 / 500000000000) (31318394677 / 50000000000) x41 := by
    apply bounds_add hx23 hx40 <;> norm_num
  let x42 : ℝ := x23-x39
  have hx42 : Bounds (313183945769 / 500000000000) (31318394677 / 50000000000) x42 := by
    exact hx41
  let x43 : ℝ := biasE (185 / 512)
  have hx43 : Bounds (313183945769 / 500000000000) (31318394677 / 50000000000) x43 := by
    simpa +zetaDelta only [biasE, div_one] using hx42
  let x44 : ℝ := biasE x0
  have hx44 : Bounds (626145967467 / 1000000000000) (31318394677 / 50000000000) x44 := by
    exact bounds_biasE hx0 (by norm_num) (by norm_num) hx22.1 hx43.2
  let x45 : ℝ := x1+x44
  have hx45 : Bounds (1319293147467 / 1000000000000) (65975753727 / 50000000000) x45 := by
    apply bounds_add hx1 hx44 <;> norm_num
  let x46 : ℝ := (2 / 1)⁻¹
  have hx46 : Bounds (1 / 2) (1 / 2) x46 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x47 : ℝ := x45*x46
  have hx47 : Bounds (659646573733 / 1000000000000) (65975753727 / 100000000000) x47 := by
    apply bounds_mul hx45 hx46 <;> norm_num
  let x48 : ℝ := x45/(2 / 1)
  have hx48 : Bounds (659646573733 / 1000000000000) (65975753727 / 100000000000) x48 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx47
  let x49 : ℝ := Real.log (2 / 1)
  have hx49 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x49 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x50 : ℝ := (1 / 1)+(32121 / 125000)
  have hx50 : Bounds (157121 / 125000) (157121 / 125000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((32121 / 125000) : ℝ)) <;> norm_num
  let x51 : ℝ := (1 / 1)+(32121 / 125000)
  have hx51 : Bounds (157121 / 125000) (157121 / 125000) x51 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((32121 / 125000) : ℝ)) <;> norm_num
  let x52 : ℝ := Real.log x51
  have hx52 : Bounds (228702471 / 1000000000) (28587809 / 125000000) x52 := by
    exact bounds_log hx51 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x53 : ℝ := x50*x52
  have hx53 : Bounds (287471687567 / 1000000000000) (11498867553 / 40000000000) x53 := by
    apply bounds_mul hx50 hx52 <;> norm_num
  let x54 : ℝ := -(32121 / 125000)
  have hx54 : Bounds (-32121 / 125000) (-32121 / 125000) x54 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((32121 / 125000) : ℝ))
  let x55 : ℝ := (1 / 1)+x54
  have hx55 : Bounds (92879 / 125000) (92879 / 125000) x55 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx54 <;> norm_num
  let x56 : ℝ := (1 / 1)-(32121 / 125000)
  have hx56 : Bounds (92879 / 125000) (92879 / 125000) x56 := by
    exact hx55
  let x57 : ℝ := -(32121 / 125000)
  have hx57 : Bounds (-32121 / 125000) (-32121 / 125000) x57 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((32121 / 125000) : ℝ))
  let x58 : ℝ := (1 / 1)+x57
  have hx58 : Bounds (92879 / 125000) (92879 / 125000) x58 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx57 <;> norm_num
  let x59 : ℝ := (1 / 1)-(32121 / 125000)
  have hx59 : Bounds (92879 / 125000) (92879 / 125000) x59 := by
    exact hx58
  let x60 : ℝ := Real.log x59
  have hx60 : Bounds (-297016167 / 1000000000) (-148508083 / 500000000) x60 := by
    exact bounds_log hx59 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x61 : ℝ := x56*x60
  have hx61 : Bounds (-220692516599 / 1000000000000) (-44138503171 / 200000000000) x61 := by
    apply bounds_mul hx56 hx60 <;> norm_num
  let x62 : ℝ := x53+x61
  have hx62 : Bounds (8347396371 / 125000000000) (6677917297 / 100000000000) x62 := by
    apply bounds_add hx53 hx61 <;> norm_num
  let x63 : ℝ := (2 / 1)⁻¹
  have hx63 : Bounds (1 / 2) (1 / 2) x63 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x64 : ℝ := x62*x63
  have hx64 : Bounds (8347396371 / 250000000000) (6677917297 / 200000000000) x64 := by
    apply bounds_mul hx62 hx63 <;> norm_num
  let x65 : ℝ := x62/(2 / 1)
  have hx65 : Bounds (8347396371 / 250000000000) (6677917297 / 200000000000) x65 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx64
  let x66 : ℝ := -x65
  have hx66 : Bounds (-6677917297 / 200000000000) (-8347396371 / 250000000000) x66 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx65
  let x67 : ℝ := x49+x66
  have hx67 : Bounds (131951518703 / 200000000000) (164939398879 / 250000000000) x67 := by
    apply bounds_add hx49 hx66 <;> norm_num
  let x68 : ℝ := x49-x65
  have hx68 : Bounds (131951518703 / 200000000000) (164939398879 / 250000000000) x68 := by
    exact hx67
  let x69 : ℝ := biasE (32121 / 125000)
  have hx69 : Bounds (131951518703 / 200000000000) (164939398879 / 250000000000) x69 := by
    simpa +zetaDelta only [biasE, div_one] using hx68
  let x70 : ℝ := Real.log (2 / 1)
  have hx70 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x70 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x71 : ℝ := (1 / 1)+(257391 / 1000000)
  have hx71 : Bounds (1257391 / 1000000) (1257391 / 1000000) x71 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((257391 / 1000000) : ℝ)) <;> norm_num
  let x72 : ℝ := (1 / 1)+(257391 / 1000000)
  have hx72 : Bounds (1257391 / 1000000) (1257391 / 1000000) x72 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((257391 / 1000000) : ℝ)) <;> norm_num
  let x73 : ℝ := Real.log x72
  have hx73 : Bounds (229038939 / 1000000000) (11451947 / 50000000) x73 := by
    exact bounds_log hx72 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x74 : ℝ := x71*x73
  have hx74 : Bounds (71997875137 / 250000000000) (143995750903 / 500000000000) x74 := by
    apply bounds_mul hx71 hx73 <;> norm_num
  let x75 : ℝ := -(257391 / 1000000)
  have hx75 : Bounds (-257391 / 1000000) (-257391 / 1000000) x75 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((257391 / 1000000) : ℝ))
  let x76 : ℝ := (1 / 1)+x75
  have hx76 : Bounds (742609 / 1000000) (742609 / 1000000) x76 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx75 <;> norm_num
  let x77 : ℝ := (1 / 1)-(257391 / 1000000)
  have hx77 : Bounds (742609 / 1000000) (742609 / 1000000) x77 := by
    exact hx76
  let x78 : ℝ := -(257391 / 1000000)
  have hx78 : Bounds (-257391 / 1000000) (-257391 / 1000000) x78 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((257391 / 1000000) : ℝ))
  let x79 : ℝ := (1 / 1)+x78
  have hx79 : Bounds (742609 / 1000000) (742609 / 1000000) x79 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx78 <;> norm_num
  let x80 : ℝ := (1 / 1)-(257391 / 1000000)
  have hx80 : Bounds (742609 / 1000000) (742609 / 1000000) x80 := by
    exact hx79
  let x81 : ℝ := Real.log x80
  have hx81 : Bounds (-148792809 / 500000000) (-297585617 / 1000000000) x81 := by
    exact bounds_log hx80 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x82 : ℝ := x77*x81
  have hx82 : Bounds (-110494879099 / 500000000000) (-110494878727 / 500000000000) x82 := by
    apply bounds_mul hx77 hx81 <;> norm_num
  let x83 : ℝ := x74+x82
  have hx83 : Bounds (1340034847 / 20000000000) (2093804511 / 31250000000) x83 := by
    apply bounds_add hx74 hx82 <;> norm_num
  let x84 : ℝ := (2 / 1)⁻¹
  have hx84 : Bounds (1 / 2) (1 / 2) x84 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x85 : ℝ := x83*x84
  have hx85 : Bounds (1340034847 / 40000000000) (2093804511 / 62500000000) x85 := by
    apply bounds_mul hx83 hx84 <;> norm_num
  let x86 : ℝ := x83/(2 / 1)
  have hx86 : Bounds (1340034847 / 40000000000) (2093804511 / 62500000000) x86 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx85
  let x87 : ℝ := -x86
  have hx87 : Bounds (-2093804511 / 62500000000) (-1340034847 / 40000000000) x87 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx86
  let x88 : ℝ := x70+x87
  have hx88 : Bounds (41227894239 / 62500000000) (26385852393 / 40000000000) x88 := by
    apply bounds_add hx70 hx87 <;> norm_num
  let x89 : ℝ := x70-x86
  have hx89 : Bounds (41227894239 / 62500000000) (26385852393 / 40000000000) x89 := by
    exact hx88
  let x90 : ℝ := biasE (257391 / 1000000)
  have hx90 : Bounds (41227894239 / 62500000000) (26385852393 / 40000000000) x90 := by
    simpa +zetaDelta only [biasE, div_one] using hx89
  let y : ℝ := doubleCapHighTailY x
  have hEll' : Real.log 2 * doubleCapHighTailFloor x = x48 := by
    simpa +zetaDelta only [div_one] using hEll
  have hy : Bounds (32121 / 125000) (257391 / 1000000) y := by
    dsimp only [y, doubleCapHighTailY]
    apply entropyInverseBias_bracket hh0.le hh1.le
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (257391 / 1000000) ≤ (26385852393 / 40000000000) := hx90.2
      have h2 : (659646573733 / 1000000000000) ≤ x48 := hx48.1
      linarith [hEll']
    · have h1 : x48 ≤ (65975753727 / 100000000000) := hx48.2
      have h2 : (131951518703 / 200000000000) ≤ biasE (32121 / 125000) := hx69.1
      linarith [hEll']
  let x91 : ℝ := x⁻¹
  have hx91 : Bounds (5526173772261 / 1000000000000) (172972972973 / 31250000000) x91 := by
    apply bounds_inv hx <;> norm_num
  let x92 : ℝ := x48*x91
  have hx92 : Bounds (145812863789 / 40000000000) (1825923562607 / 500000000000) x92 := by
    apply bounds_mul hx48 hx91 <;> norm_num
  let x93 : ℝ := x48/x
  have hx93 : Bounds (145812863789 / 40000000000) (1825923562607 / 500000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(185089 / 1000000)
  have hx95 : Bounds (1185089 / 1000000) (1185089 / 1000000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((185089 / 1000000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(185089 / 1000000)
  have hx96 : Bounds (1185089 / 1000000) (1185089 / 1000000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((185089 / 1000000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (169817877 / 1000000000) (84908939 / 500000000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (50312324509 / 250000000000) (100624649611 / 500000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(185089 / 1000000)
  have hx99 : Bounds (-185089 / 1000000) (-185089 / 1000000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((185089 / 1000000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (814911 / 1000000) (814911 / 1000000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(185089 / 1000000)
  have hx101 : Bounds (814911 / 1000000) (814911 / 1000000) x101 := by
    exact hx100
  let x102 : ℝ := -(185089 / 1000000)
  have hx102 : Bounds (-185089 / 1000000) (-185089 / 1000000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((185089 / 1000000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (814911 / 1000000) (814911 / 1000000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(185089 / 1000000)
  have hx104 : Bounds (814911 / 1000000) (814911 / 1000000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-1637411 / 8000000) (-102338187 / 500000000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-41698257357 / 250000000000) (-41698257153 / 250000000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (538379197 / 15625000000) (3445627061 / 100000000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (538379197 / 31250000000) (3445627061 / 200000000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (538379197 / 31250000000) (3445627061 / 200000000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-3445627061 / 200000000000) (-538379197 / 31250000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (135183808939 / 200000000000) (84489880837 / 125000000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (135183808939 / 200000000000) (84489880837 / 125000000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (185089 / 1000000)
  have hx114 : Bounds (135183808939 / 200000000000) (84489880837 / 125000000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(37081 / 200000)
  have hx116 : Bounds (237081 / 200000) (237081 / 200000) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((37081 / 200000) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(37081 / 200000)
  have hx117 : Bounds (237081 / 200000) (237081 / 200000) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((37081 / 200000) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (21260561 / 125000000) (170084489 / 1000000000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (201619002497 / 1000000000000) (50404750921 / 250000000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(37081 / 200000)
  have hx120 : Bounds (-37081 / 200000) (-37081 / 200000) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((37081 / 200000) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (162919 / 200000) (162919 / 200000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(37081 / 200000)
  have hx122 : Bounds (162919 / 200000) (162919 / 200000) x122 := by
    exact hx121
  let x123 : ℝ := -(37081 / 200000)
  have hx123 : Bounds (-37081 / 200000) (-37081 / 200000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((37081 / 200000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (162919 / 200000) (162919 / 200000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(37081 / 200000)
  have hx125 : Bounds (162919 / 200000) (162919 / 200000) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-102532111 / 500000000) (-205064221 / 1000000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-167044289921 / 1000000000000) (-33408857821 / 200000000000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (135057471 / 3906250000) (34574714579 / 1000000000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (135057471 / 7812500000) (1728735729 / 100000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (135057471 / 7812500000) (1728735729 / 100000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-1728735729 / 100000000000) (-135057471 / 7812500000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (67585982271 / 100000000000) (84482478089 / 125000000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (67585982271 / 100000000000) (84482478089 / 125000000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (37081 / 200000)
  have hx135 : Bounds (67585982271 / 100000000000) (84482478089 / 125000000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(185089 / 1000000)
  have hx136 : Bounds (337354464323 / 500000000000) (675916732559 / 1000000000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((185089 / 1000000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(37081 / 200000)
  have hx137 : Bounds (675860850269 / 1000000000000) (677070716251 / 1000000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((37081 / 200000) : ℝ)) <;> norm_num
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
  have hc : Bounds (185089 / 1000000) (37081 / 200000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num)
      (by norm_num) (show 0 < x93 by linarith [hx93.1]) hcEq
    · have h1 : x93 * (185089 / 1000000) ≤ (675916732559 / 1000000000000) := hx136.2
      have h2 : (135183808939 / 200000000000) ≤ biasE (185089 / 1000000) := hx114.1
      linarith
    · have h1 : biasE (37081 / 200000) ≤ (84482478089 / 125000000000) := hx135.2
      have h2 : (675860850269 / 1000000000000) ≤ x93 * (37081 / 200000) := hx137.1
      linarith
  let x138 : ℝ := (1 / 1)+x0
  have hx138 : Bounds (697 / 512) (6973 / 5120) x138 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx0 <;> norm_num
  let x139 : ℝ := -x0
  have hx139 : Bounds (-1853 / 5120) (-185 / 512) x139 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x140 : ℝ := (1 / 1)+x139
  have hx140 : Bounds (3267 / 5120) (327 / 512) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx139 <;> norm_num
  let x141 : ℝ := (1 / 1)-x0
  have hx141 : Bounds (3267 / 5120) (327 / 512) x141 := by
    exact hx140
  let x142 : ℝ := x141⁻¹
  have hx142 : Bounds (782874617737 / 500000000000) (1567187021733 / 1000000000000) x142 := by
    apply bounds_inv hx141 <;> norm_num
  let x143 : ℝ := x138*x142
  have hx143 : Bounds (532874617737 / 250000000000) (1067187021733 / 500000000000) x143 := by
    apply bounds_mul hx138 hx142 <;> norm_num
  let x144 : ℝ := x138/x141
  have hx144 : Bounds (532874617737 / 250000000000) (1067187021733 / 500000000000) x144 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx143
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (756825239 / 1000000000) (758173417 / 1000000000) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_14.2)
  let x146 : ℝ := (2 / 1)⁻¹
  have hx146 : Bounds (1 / 2) (1 / 2) x146 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x147 : ℝ := x145*x146
  have hx147 : Bounds (756825239 / 2000000000) (758173417 / 2000000000) x147 := by
    apply bounds_mul hx145 hx146 <;> norm_num
  let x148 : ℝ := x145/(2 / 1)
  have hx148 : Bounds (756825239 / 2000000000) (758173417 / 2000000000) x148 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx147
  let x149 : ℝ := (1 / 1)+y
  have hx149 : Bounds (157121 / 125000) (1257391 / 1000000) x149 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x150 : ℝ := -y
  have hx150 : Bounds (-257391 / 1000000) (-32121 / 125000) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (742609 / 1000000) (92879 / 125000) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-y
  have hx152 : Bounds (742609 / 1000000) (92879 / 125000) x152 := by
    exact hx151
  let x153 : ℝ := x152⁻¹
  have hx153 : Bounds (269167411363 / 200000000000) (134660366357 / 100000000000) x153 := by
    apply bounds_inv hx152 <;> norm_num
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (169167411363 / 100000000000) (84660366357 / 50000000000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x149/x152
  have hx155 : Bounds (169167411363 / 100000000000) (84660366357 / 50000000000) x155 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx154
  let x156 : ℝ := Real.log x155
  have hx156 : Bounds (262859319 / 500000000) (263312279 / 500000000) x156 := by
    exact bounds_log hx155 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_16.2)
  let x157 : ℝ := (2 / 1)⁻¹
  have hx157 : Bounds (1 / 2) (1 / 2) x157 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x158 : ℝ := x156*x157
  have hx158 : Bounds (262859319 / 1000000000) (263312279 / 1000000000) x158 := by
    apply bounds_mul hx156 hx157 <;> norm_num
  let x159 : ℝ := x156/(2 / 1)
  have hx159 : Bounds (262859319 / 1000000000) (263312279 / 1000000000) x159 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx158
  let x160 : ℝ := (1 / 1)+c
  have hx160 : Bounds (1185089 / 1000000) (237081 / 200000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x161 : ℝ := -c
  have hx161 : Bounds (-37081 / 200000) (-185089 / 1000000) x161 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x162 : ℝ := (1 / 1)+x161
  have hx162 : Bounds (162919 / 200000) (814911 / 1000000) x162 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx161 <;> norm_num
  let x163 : ℝ := (1 / 1)-c
  have hx163 : Bounds (162919 / 200000) (814911 / 1000000) x163 := by
    exact hx162
  let x164 : ℝ := x163⁻¹
  have hx164 : Bounds (245425574081 / 200000000000) (613801950663 / 500000000000) x164 := by
    apply bounds_inv hx163 <;> norm_num
  let x165 : ℝ := x160*x164
  have hx165 : Bounds (145425574081 / 100000000000) (363801950663 / 250000000000) x165 := by
    apply bounds_mul hx160 hx164 <;> norm_num
  let x166 : ℝ := x160/x163
  have hx166 : Bounds (145425574081 / 100000000000) (363801950663 / 250000000000) x166 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx165
  let x167 : ℝ := Real.log x166
  have hx167 : Bounds (374494251 / 1000000000) (375148711 / 1000000000) x167 := by
    exact bounds_log hx166 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x168 : ℝ := (2 / 1)⁻¹
  have hx168 : Bounds (1 / 2) (1 / 2) x168 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x169 : ℝ := x167*x168
  have hx169 : Bounds (374494251 / 2000000000) (375148711 / 2000000000) x169 := by
    apply bounds_mul hx167 hx168 <;> norm_num
  let x170 : ℝ := x167/(2 / 1)
  have hx170 : Bounds (374494251 / 2000000000) (375148711 / 2000000000) x170 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx169
  let x171 : ℝ := Real.log (2 / 1)
  have hx171 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x171 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x172 : ℝ := c*c
  have hx172 : Bounds (34257937921 / 1000000000000) (1375000561 / 40000000000) x172 := by
    apply bounds_mul hc hc <;> norm_num
  let x173 : ℝ := -x172
  have hx173 : Bounds (-1375000561 / 40000000000) (-34257937921 / 1000000000000) x173 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx172
  let x174 : ℝ := (1 / 1)+x173
  have hx174 : Bounds (38624999439 / 40000000000) (965742062079 / 1000000000000) x174 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx173 <;> norm_num
  let x175 : ℝ := (1 / 1)-x172
  have hx175 : Bounds (38624999439 / 40000000000) (965742062079 / 1000000000000) x175 := by
    exact hx174
  let x176 : ℝ := Real.log x175
  have hx176 : Bounds (-17489867 / 500000000) (-68083 / 1953125) x176 := by
    exact bounds_log hx175 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (-17489867 / 1000000000) (-68083 / 3906250) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (-17489867 / 1000000000) (-68083 / 3906250) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (68083 / 3906250) (17489867 / 1000000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x171+x180
  have hx181 : Bounds (177644107 / 250000000) (88829631 / 125000000) x181 := by
    apply bounds_add hx171 hx180 <;> norm_num
  let x182 : ℝ := x171-x179
  have hx182 : Bounds (177644107 / 250000000) (88829631 / 125000000) x182 := by
    exact hx181
  let x183 : ℝ := Real.log (2 / 1)
  have hx183 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x183 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x184 : ℝ := (1 / 1)+(37081 / 200000)
  have hx184 : Bounds (237081 / 200000) (237081 / 200000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((37081 / 200000) : ℝ)) <;> norm_num
  let x185 : ℝ := (1 / 1)+(37081 / 200000)
  have hx185 : Bounds (237081 / 200000) (237081 / 200000) x185 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((37081 / 200000) : ℝ)) <;> norm_num
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (21260561 / 125000000) (170084489 / 1000000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x187 : ℝ := x184*x186
  have hx187 : Bounds (201619002497 / 1000000000000) (50404750921 / 250000000000) x187 := by
    apply bounds_mul hx184 hx186 <;> norm_num
  let x188 : ℝ := -(37081 / 200000)
  have hx188 : Bounds (-37081 / 200000) (-37081 / 200000) x188 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((37081 / 200000) : ℝ))
  let x189 : ℝ := (1 / 1)+x188
  have hx189 : Bounds (162919 / 200000) (162919 / 200000) x189 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx188 <;> norm_num
  let x190 : ℝ := (1 / 1)-(37081 / 200000)
  have hx190 : Bounds (162919 / 200000) (162919 / 200000) x190 := by
    exact hx189
  let x191 : ℝ := -(37081 / 200000)
  have hx191 : Bounds (-37081 / 200000) (-37081 / 200000) x191 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((37081 / 200000) : ℝ))
  let x192 : ℝ := (1 / 1)+x191
  have hx192 : Bounds (162919 / 200000) (162919 / 200000) x192 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx191 <;> norm_num
  let x193 : ℝ := (1 / 1)-(37081 / 200000)
  have hx193 : Bounds (162919 / 200000) (162919 / 200000) x193 := by
    exact hx192
  let x194 : ℝ := Real.log x193
  have hx194 : Bounds (-102532111 / 500000000) (-205064221 / 1000000000) x194 := by
    exact bounds_log hx193 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x195 : ℝ := x190*x194
  have hx195 : Bounds (-167044289921 / 1000000000000) (-33408857821 / 200000000000) x195 := by
    apply bounds_mul hx190 hx194 <;> norm_num
  let x196 : ℝ := x187+x195
  have hx196 : Bounds (135057471 / 3906250000) (34574714579 / 1000000000000) x196 := by
    apply bounds_add hx187 hx195 <;> norm_num
  let x197 : ℝ := (2 / 1)⁻¹
  have hx197 : Bounds (1 / 2) (1 / 2) x197 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x198 : ℝ := x196*x197
  have hx198 : Bounds (135057471 / 7812500000) (1728735729 / 100000000000) x198 := by
    apply bounds_mul hx196 hx197 <;> norm_num
  let x199 : ℝ := x196/(2 / 1)
  have hx199 : Bounds (135057471 / 7812500000) (1728735729 / 100000000000) x199 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx198
  let x200 : ℝ := -x199
  have hx200 : Bounds (-1728735729 / 100000000000) (-135057471 / 7812500000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx199
  let x201 : ℝ := x183+x200
  have hx201 : Bounds (67585982271 / 100000000000) (84482478089 / 125000000000) x201 := by
    apply bounds_add hx183 hx200 <;> norm_num
  let x202 : ℝ := x183-x199
  have hx202 : Bounds (67585982271 / 100000000000) (84482478089 / 125000000000) x202 := by
    exact hx201
  let x203 : ℝ := biasE (37081 / 200000)
  have hx203 : Bounds (67585982271 / 100000000000) (84482478089 / 125000000000) x203 := by
    simpa +zetaDelta only [biasE, div_one] using hx202
  let x204 : ℝ := Real.log (2 / 1)
  have hx204 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x204 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x205 : ℝ := (1 / 1)+(185089 / 1000000)
  have hx205 : Bounds (1185089 / 1000000) (1185089 / 1000000) x205 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((185089 / 1000000) : ℝ)) <;> norm_num
  let x206 : ℝ := (1 / 1)+(185089 / 1000000)
  have hx206 : Bounds (1185089 / 1000000) (1185089 / 1000000) x206 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((185089 / 1000000) : ℝ)) <;> norm_num
  let x207 : ℝ := Real.log x206
  have hx207 : Bounds (169817877 / 1000000000) (84908939 / 500000000) x207 := by
    exact bounds_log hx206 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x208 : ℝ := x205*x207
  have hx208 : Bounds (50312324509 / 250000000000) (100624649611 / 500000000000) x208 := by
    apply bounds_mul hx205 hx207 <;> norm_num
  let x209 : ℝ := -(185089 / 1000000)
  have hx209 : Bounds (-185089 / 1000000) (-185089 / 1000000) x209 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((185089 / 1000000) : ℝ))
  let x210 : ℝ := (1 / 1)+x209
  have hx210 : Bounds (814911 / 1000000) (814911 / 1000000) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx209 <;> norm_num
  let x211 : ℝ := (1 / 1)-(185089 / 1000000)
  have hx211 : Bounds (814911 / 1000000) (814911 / 1000000) x211 := by
    exact hx210
  let x212 : ℝ := -(185089 / 1000000)
  have hx212 : Bounds (-185089 / 1000000) (-185089 / 1000000) x212 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((185089 / 1000000) : ℝ))
  let x213 : ℝ := (1 / 1)+x212
  have hx213 : Bounds (814911 / 1000000) (814911 / 1000000) x213 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx212 <;> norm_num
  let x214 : ℝ := (1 / 1)-(185089 / 1000000)
  have hx214 : Bounds (814911 / 1000000) (814911 / 1000000) x214 := by
    exact hx213
  let x215 : ℝ := Real.log x214
  have hx215 : Bounds (-1637411 / 8000000) (-102338187 / 500000000) x215 := by
    exact bounds_log hx214 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x216 : ℝ := x211*x215
  have hx216 : Bounds (-41698257357 / 250000000000) (-41698257153 / 250000000000) x216 := by
    apply bounds_mul hx211 hx215 <;> norm_num
  let x217 : ℝ := x208+x216
  have hx217 : Bounds (538379197 / 15625000000) (3445627061 / 100000000000) x217 := by
    apply bounds_add hx208 hx216 <;> norm_num
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (538379197 / 31250000000) (3445627061 / 200000000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (538379197 / 31250000000) (3445627061 / 200000000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := -x220
  have hx221 : Bounds (-3445627061 / 200000000000) (-538379197 / 31250000000) x221 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx220
  let x222 : ℝ := x204+x221
  have hx222 : Bounds (135183808939 / 200000000000) (84489880837 / 125000000000) x222 := by
    apply bounds_add hx204 hx221 <;> norm_num
  let x223 : ℝ := x204-x220
  have hx223 : Bounds (135183808939 / 200000000000) (84489880837 / 125000000000) x223 := by
    exact hx222
  let x224 : ℝ := biasE (185089 / 1000000)
  have hx224 : Bounds (135183808939 / 200000000000) (84489880837 / 125000000000) x224 := by
    simpa +zetaDelta only [biasE, div_one] using hx223
  let x225 : ℝ := biasE c
  have hx225 : Bounds (67585982271 / 100000000000) (84489880837 / 125000000000) x225 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx203.1 hx224.2
  let x226 : ℝ := x159⁻¹
  have hx226 : Bounds (3797771998319 / 1000000000000) (3804316330897 / 1000000000000) x226 := by
    apply bounds_inv hx159 <;> norm_num
  let x227 : ℝ := x148*x226
  have hx227 : Bounds (1437124850147 / 1000000000000) (1442165755973 / 1000000000000) x227 := by
    apply bounds_mul hx148 hx226 <;> norm_num
  let x228 : ℝ := x148/x159
  have hx228 : Bounds (1437124850147 / 1000000000000) (1442165755973 / 1000000000000) x228 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx227
  let x229 : ℝ := c*x148
  have hx229 : Bounds (7004001333 / 100000000000) (7028457119 / 100000000000) x229 := by
    apply bounds_mul hc hx148 <;> norm_num
  let x230 : ℝ := x225+x229
  have hx230 : Bounds (18647495901 / 25000000000) (373101808943 / 500000000000) x230 := by
    apply bounds_add hx225 hx229 <;> norm_num
  let x231 : ℝ := x*x170
  have hx231 : Bounds (2114301649 / 62500000000) (3394289851 / 100000000000) x231 := by
    apply bounds_mul hx hx170 <;> norm_num
  let x232 : ℝ := x48+x231
  have hx232 : Bounds (693475400117 / 1000000000000) (34685021789 / 50000000000) x232 := by
    apply bounds_add hx48 hx231 <;> norm_num
  let x233 : ℝ := x232⁻¹
  have hx233 : Bounds (1441544431027 / 1000000000000) (288402443643 / 200000000000) x233 := by
    apply bounds_inv hx232 <;> norm_num
  let x234 : ℝ := x230*x233
  have hx234 : Bounds (1075247754747 / 1000000000000) (269008683567 / 250000000000) x234 := by
    apply bounds_mul hx230 hx233 <;> norm_num
  let x235 : ℝ := x230/x232
  have hx235 : Bounds (1075247754747 / 1000000000000) (269008683567 / 250000000000) x235 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx234
  let x236 : ℝ := y*y
  have hx236 : Bounds (1031758641 / 15625000000) (66250126881 / 1000000000000) x236 := by
    apply bounds_mul hy hy <;> norm_num
  let x237 : ℝ := -x236
  have hx237 : Bounds (-66250126881 / 1000000000000) (-1031758641 / 15625000000) x237 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx236
  let x238 : ℝ := (1 / 1)+x237
  have hx238 : Bounds (933749873119 / 1000000000000) (14593241359 / 15625000000) x238 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx237 <;> norm_num
  let x239 : ℝ := (1 / 1)-x236
  have hx239 : Bounds (933749873119 / 1000000000000) (14593241359 / 15625000000) x239 := by
    exact hx238
  let x240 : ℝ := x239*x159
  have hx240 : Bounds (61361213941 / 250000000000) (15370318561 / 62500000000) x240 := by
    apply bounds_mul hx239 hx159 <;> norm_num
  let x241 : ℝ := c*c
  have hx241 : Bounds (34257937921 / 1000000000000) (1375000561 / 40000000000) x241 := by
    apply bounds_mul hc hc <;> norm_num
  let x242 : ℝ := -x241
  have hx242 : Bounds (-1375000561 / 40000000000) (-34257937921 / 1000000000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx241
  let x243 : ℝ := (1 / 1)+x242
  have hx243 : Bounds (38624999439 / 40000000000) (965742062079 / 1000000000000) x243 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx242 <;> norm_num
  let x244 : ℝ := (1 / 1)-x241
  have hx244 : Bounds (38624999439 / 40000000000) (965742062079 / 1000000000000) x244 := by
    exact hx243
  let x245 : ℝ := x244*x182
  have hx245 : Bounds (686150353321 / 1000000000000) (343146044063 / 500000000000) x245 := by
    apply bounds_mul hx244 hx182 <;> norm_num
  let x246 : ℝ := y*y
  have hx246 : Bounds (1031758641 / 15625000000) (66250126881 / 1000000000000) x246 := by
    apply bounds_mul hy hy <;> norm_num
  let x247 : ℝ := (1 / 1)+x246
  have hx247 : Bounds (16656758641 / 15625000000) (1066250126881 / 1000000000000) x247 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx246 <;> norm_num
  let x248 : ℝ := x247*x159
  have hx248 : Bounds (280216590919 / 1000000000000) (140378375447 / 500000000000) x248 := by
    apply bounds_mul hx247 hx159 <;> norm_num
  let x249 : ℝ := -y
  have hx249 : Bounds (-257391 / 1000000) (-32121 / 125000) x249 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x250 : ℝ := x248+x249
  have hx250 : Bounds (22825590919 / 1000000000000) (11894375447 / 500000000000) x250 := by
    apply bounds_add hx248 hx249 <;> norm_num
  let x251 : ℝ := x248-y
  have hx251 : Bounds (22825590919 / 1000000000000) (11894375447 / 500000000000) x251 := by
    exact hx250
  let x252 : ℝ := x240*x240
  have hx252 : Bounds (60243177221 / 1000000000000) (60479153323 / 1000000000000) x252 := by
    apply bounds_mul hx240 hx240 <;> norm_num
  let x253 : ℝ := x252⁻¹
  have hx253 : Bounds (16534623007357 / 1000000000000) (1659939010739 / 100000000000) x253 := by
    apply bounds_inv hx252 <;> norm_num
  let x254 : ℝ := x251*x253
  have hx254 : Bounds (75482508153 / 200000000000) (197439378129 / 500000000000) x254 := by
    apply bounds_mul hx251 hx253 <;> norm_num
  let x255 : ℝ := x251/x252
  have hx255 : Bounds (75482508153 / 200000000000) (197439378129 / 500000000000) x255 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx254
  let x256 : ℝ := (-2 / 1)*x255
  have hx256 : Bounds (-197439378129 / 250000000000) (-75482508153 / 100000000000) x256 := by
    apply bounds_mul (bounds_const ((-2 / 1) : ℝ)) hx255 <;> norm_num
  let x257 : ℝ := x256*x228
  have hx257 : Bounds (-1138961240073 / 1000000000000) (-54238894109 / 50000000000) x257 := by
    apply bounds_mul hx256 hx228 <;> norm_num
  let x258 : ℝ := (2 / 1)*x182
  have hx258 : Bounds (177644107 / 125000000) (88829631 / 62500000) x258 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx182 <;> norm_num
  let x259 : ℝ := c*c
  have hx259 : Bounds (34257937921 / 1000000000000) (1375000561 / 40000000000) x259 := by
    apply bounds_mul hc hc <;> norm_num
  let x260 : ℝ := -x259
  have hx260 : Bounds (-1375000561 / 40000000000) (-34257937921 / 1000000000000) x260 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx259
  let x261 : ℝ := x258+x260
  have hx261 : Bounds (55471113679 / 40000000000) (1387016158079 / 1000000000000) x261 := by
    apply bounds_add hx258 hx260 <;> norm_num
  let x262 : ℝ := x258-x259
  have hx262 : Bounds (55471113679 / 40000000000) (1387016158079 / 1000000000000) x262 := by
    exact hx261
  let x263 : ℝ := c*x262
  have hx263 : Bounds (256677323993 / 1000000000000) (257159730789 / 1000000000000) x263 := by
    apply bounds_mul hc hx262 <;> norm_num
  let x264 : ℝ := x245*x245
  have hx264 : Bounds (235401153681 / 500000000000) (18839873209 / 40000000000) x264 := by
    apply bounds_mul hx245 hx245 <;> norm_num
  let x265 : ℝ := x264⁻¹
  have hx265 : Bounds (1061578269563 / 500000000000) (53100844259 / 25000000000) x265 := by
    apply bounds_inv hx264 <;> norm_num
  let x266 : ℝ := x263*x265
  have hx266 : Bounds (544966138881 / 1000000000000) (546215952573 / 1000000000000) x266 := by
    apply bounds_mul hx263 hx265 <;> norm_num
  let x267 : ℝ := x263/x264
  have hx267 : Bounds (544966138881 / 1000000000000) (546215952573 / 1000000000000) x267 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx266
  let x268 : ℝ := (2 / 1)*x267
  have hx268 : Bounds (544966138881 / 500000000000) (546215952573 / 500000000000) x268 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx267 <;> norm_num
  let x269 : ℝ := x268*x235
  have hx269 : Bounds (1171947234489 / 1000000000000) (29387366869 / 25000000000) x269 := by
    apply bounds_mul hx268 hx235 <;> norm_num
  let x270 : ℝ := x257+x269
  have hx270 : Bounds (2061624651 / 62500000000) (4535839629 / 50000000000) x270 := by
    apply bounds_add hx257 hx269 <;> norm_num
  have hPos : 0 < x270 :=
    lt_of_lt_of_le (by norm_num) hx270.1
  have hBridgeL : doubleCapBridgeL x = x48 := by
    exact hEll'
  rw [← doubleCapBridgeDerivativeTraceForm_eq x]
  simpa +zetaDelta only [doubleCapBridgeDerivativeTraceForm,
    hBridgeL, SmallMean.A, biasB, div_one, pow_two] using hPos

theorem acceptedCell : DoubleCapBridgeDerivativeCellCertificate
    (⟨190, by decide⟩ : Fin 256) doubleCapBridgeDerivativeExpression where
  positive x hx := by
    have hloEq : doubleCapBridgeLo (⟨190, by decide⟩ : Fin 256) =
        (185 / 1024) := by norm_num [doubleCapBridgeLo, doubleCapBridgeStep]
    have hhiEq : doubleCapBridgeHi (⟨190, by decide⟩ : Fin 256) =
        (1853 / 10240) := by norm_num [doubleCapBridgeHi, doubleCapBridgeStep]
    have hlo : (185 / 1024) ≤ x := by
      simpa only [hloEq] using hx.1
    have hhi : x ≤ (1853 / 10240) := by
      simpa only [hhiEq] using hx.2
    exact cell_derivative_pos x ⟨hlo, hhi⟩

#print axioms cell_derivative_pos
#print axioms acceptedCell

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell190

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell191 =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell191
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_derivative_pos (x : ℝ)
    (hx : Bounds (1853 / 10240) (29 / 160) x) :
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
  have hx0 : Bounds (1853 / 5120) (29 / 80) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx <;> norm_num
  let x1 : ℝ := Real.log (2 / 1)
  have hx1 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x1 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x2 : ℝ := Real.log (2 / 1)
  have hx2 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x2 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x3 : ℝ := (1 / 1)+(29 / 80)
  have hx3 : Bounds (109 / 80) (109 / 80) x3 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((29 / 80) : ℝ)) <;> norm_num
  let x4 : ℝ := (1 / 1)+(29 / 80)
  have hx4 : Bounds (109 / 80) (109 / 80) x4 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((29 / 80) : ℝ)) <;> norm_num
  let x5 : ℝ := Real.log x4
  have hx5 : Bounds (309321247 / 1000000000) (9666289 / 31250000) x5 := by
    exact bounds_log hx4 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x6 : ℝ := x3*x5
  have hx6 : Bounds (421450199037 / 1000000000000) (1053625501 / 2500000000) x6 := by
    apply bounds_mul hx3 hx5 <;> norm_num
  let x7 : ℝ := -(29 / 80)
  have hx7 : Bounds (-29 / 80) (-29 / 80) x7 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((29 / 80) : ℝ))
  let x8 : ℝ := (1 / 1)+x7
  have hx8 : Bounds (51 / 80) (51 / 80) x8 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx7 <;> norm_num
  let x9 : ℝ := (1 / 1)-(29 / 80)
  have hx9 : Bounds (51 / 80) (51 / 80) x9 := by
    exact hx8
  let x10 : ℝ := -(29 / 80)
  have hx10 : Bounds (-29 / 80) (-29 / 80) x10 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((29 / 80) : ℝ))
  let x11 : ℝ := (1 / 1)+x10
  have hx11 : Bounds (51 / 80) (51 / 80) x11 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx10 <;> norm_num
  let x12 : ℝ := (1 / 1)-(29 / 80)
  have hx12 : Bounds (51 / 80) (51 / 80) x12 := by
    exact hx11
  let x13 : ℝ := Real.log x12
  have hx13 : Bounds (-225100501 / 500000000) (-450201001 / 1000000000) x13 := by
    exact bounds_log hx12 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x14 : ℝ := x9*x13
  have hx14 : Bounds (-11480125551 / 40000000000) (-287003138137 / 1000000000000) x14 := by
    apply bounds_mul hx9 hx13 <;> norm_num
  let x15 : ℝ := x6+x14
  have hx15 : Bounds (67223530131 / 500000000000) (134447062263 / 1000000000000) x15 := by
    apply bounds_add hx6 hx14 <;> norm_num
  let x16 : ℝ := (2 / 1)⁻¹
  have hx16 : Bounds (1 / 2) (1 / 2) x16 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x17 : ℝ := x15*x16
  have hx17 : Bounds (67223530131 / 1000000000000) (16805882783 / 250000000000) x17 := by
    apply bounds_mul hx15 hx16 <;> norm_num
  let x18 : ℝ := x15/(2 / 1)
  have hx18 : Bounds (67223530131 / 1000000000000) (16805882783 / 250000000000) x18 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx17
  let x19 : ℝ := -x18
  have hx19 : Bounds (-16805882783 / 250000000000) (-67223530131 / 1000000000000) x19 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx18
  let x20 : ℝ := x2+x19
  have hx20 : Bounds (156480912217 / 250000000000) (625923650869 / 1000000000000) x20 := by
    apply bounds_add hx2 hx19 <;> norm_num
  let x21 : ℝ := x2-x18
  have hx21 : Bounds (156480912217 / 250000000000) (625923650869 / 1000000000000) x21 := by
    exact hx20
  let x22 : ℝ := biasE (29 / 80)
  have hx22 : Bounds (156480912217 / 250000000000) (625923650869 / 1000000000000) x22 := by
    simpa +zetaDelta only [biasE, div_one] using hx21
  let x23 : ℝ := Real.log (2 / 1)
  have hx23 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x23 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x24 : ℝ := (1 / 1)+(1853 / 5120)
  have hx24 : Bounds (6973 / 5120) (6973 / 5120) x24 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1853 / 5120) : ℝ)) <;> norm_num
  let x25 : ℝ := (1 / 1)+(1853 / 5120)
  have hx25 : Bounds (6973 / 5120) (6973 / 5120) x25 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1853 / 5120) : ℝ)) <;> norm_num
  let x26 : ℝ := Real.log x25
  have hx26 : Bounds (308891109 / 1000000000) (30889111 / 100000000) x26 := by
    exact bounds_log hx25 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x27 : ℝ := x24*x26
  have hx27 : Bounds (52585393141 / 125000000000) (420683146491 / 1000000000000) x27 := by
    apply bounds_mul hx24 hx26 <;> norm_num
  let x28 : ℝ := -(1853 / 5120)
  have hx28 : Bounds (-1853 / 5120) (-1853 / 5120) x28 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1853 / 5120) : ℝ))
  let x29 : ℝ := (1 / 1)+x28
  have hx29 : Bounds (3267 / 5120) (3267 / 5120) x29 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx28 <;> norm_num
  let x30 : ℝ := (1 / 1)-(1853 / 5120)
  have hx30 : Bounds (3267 / 5120) (3267 / 5120) x30 := by
    exact hx29
  let x31 : ℝ := -(1853 / 5120)
  have hx31 : Bounds (-1853 / 5120) (-1853 / 5120) x31 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1853 / 5120) : ℝ))
  let x32 : ℝ := (1 / 1)+x31
  have hx32 : Bounds (3267 / 5120) (3267 / 5120) x32 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx31 <;> norm_num
  let x33 : ℝ := (1 / 1)-(1853 / 5120)
  have hx33 : Bounds (3267 / 5120) (3267 / 5120) x33 := by
    exact hx32
  let x34 : ℝ := Real.log x33
  have hx34 : Bounds (-449282307 / 1000000000) (-224641153 / 500000000) x34 := by
    exact bounds_log hx33 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x35 : ℝ := x30*x34
  have hx35 : Bounds (-57336144413 / 200000000000) (-143340360713 / 500000000000) x35 := by
    apply bounds_mul hx30 hx34 <;> norm_num
  let x36 : ℝ := x27+x35
  have hx36 : Bounds (134002423063 / 1000000000000) (26800485013 / 200000000000) x36 := by
    apply bounds_add hx27 hx35 <;> norm_num
  let x37 : ℝ := (2 / 1)⁻¹
  have hx37 : Bounds (1 / 2) (1 / 2) x37 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x38 : ℝ := x36*x37
  have hx38 : Bounds (67001211531 / 1000000000000) (67001212533 / 1000000000000) x38 := by
    apply bounds_mul hx36 hx37 <;> norm_num
  let x39 : ℝ := x36/(2 / 1)
  have hx39 : Bounds (67001211531 / 1000000000000) (67001212533 / 1000000000000) x39 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx38
  let x40 : ℝ := -x39
  have hx40 : Bounds (-67001212533 / 1000000000000) (-67001211531 / 1000000000000) x40 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx39
  let x41 : ℝ := x23+x40
  have hx41 : Bounds (626145967467 / 1000000000000) (626145969469 / 1000000000000) x41 := by
    apply bounds_add hx23 hx40 <;> norm_num
  let x42 : ℝ := x23-x39
  have hx42 : Bounds (626145967467 / 1000000000000) (626145969469 / 1000000000000) x42 := by
    exact hx41
  let x43 : ℝ := biasE (1853 / 5120)
  have hx43 : Bounds (626145967467 / 1000000000000) (626145969469 / 1000000000000) x43 := by
    simpa +zetaDelta only [biasE, div_one] using hx42
  let x44 : ℝ := biasE x0
  have hx44 : Bounds (156480912217 / 250000000000) (626145969469 / 1000000000000) x44 := by
    exact bounds_biasE hx0 (by norm_num) (by norm_num) hx22.1 hx43.2
  let x45 : ℝ := x1+x44
  have hx45 : Bounds (329767707217 / 250000000000) (1319293150469 / 1000000000000) x45 := by
    apply bounds_add hx1 hx44 <;> norm_num
  let x46 : ℝ := (2 / 1)⁻¹
  have hx46 : Bounds (1 / 2) (1 / 2) x46 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x47 : ℝ := x45*x46
  have hx47 : Bounds (329767707217 / 500000000000) (131929315047 / 200000000000) x47 := by
    apply bounds_mul hx45 hx46 <;> norm_num
  let x48 : ℝ := x45/(2 / 1)
  have hx48 : Bounds (329767707217 / 500000000000) (131929315047 / 200000000000) x48 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx47
  let x49 : ℝ := Real.log (2 / 1)
  have hx49 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x49 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x50 : ℝ := (1 / 1)+(257389 / 1000000)
  have hx50 : Bounds (1257389 / 1000000) (1257389 / 1000000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((257389 / 1000000) : ℝ)) <;> norm_num
  let x51 : ℝ := (1 / 1)+(257389 / 1000000)
  have hx51 : Bounds (1257389 / 1000000) (1257389 / 1000000) x51 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((257389 / 1000000) : ℝ)) <;> norm_num
  let x52 : ℝ := Real.log x51
  have hx52 : Bounds (57259337 / 250000000) (229037349 / 1000000000) x52 := by
    exact bounds_log hx51 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x53 : ℝ := x50*x52
  have hx53 : Bounds (71997260491 / 250000000000) (143994521611 / 500000000000) x53 := by
    apply bounds_mul hx50 hx52 <;> norm_num
  let x54 : ℝ := -(257389 / 1000000)
  have hx54 : Bounds (-257389 / 1000000) (-257389 / 1000000) x54 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((257389 / 1000000) : ℝ))
  let x55 : ℝ := (1 / 1)+x54
  have hx55 : Bounds (742611 / 1000000) (742611 / 1000000) x55 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx54 <;> norm_num
  let x56 : ℝ := (1 / 1)-(257389 / 1000000)
  have hx56 : Bounds (742611 / 1000000) (742611 / 1000000) x56 := by
    exact hx55
  let x57 : ℝ := -(257389 / 1000000)
  have hx57 : Bounds (-257389 / 1000000) (-257389 / 1000000) x57 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((257389 / 1000000) : ℝ))
  let x58 : ℝ := (1 / 1)+x57
  have hx58 : Bounds (742611 / 1000000) (742611 / 1000000) x58 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx57 <;> norm_num
  let x59 : ℝ := (1 / 1)-(257389 / 1000000)
  have hx59 : Bounds (742611 / 1000000) (742611 / 1000000) x59 := by
    exact hx58
  let x60 : ℝ := Real.log x59
  have hx60 : Bounds (-11903317 / 40000000) (-74395731 / 250000000) x60 := by
    exact bounds_log hx59 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x61 : ℝ := x56*x60
  have hx61 : Bounds (-110494176759 / 500000000000) (-110494176387 / 500000000000) x61 := by
    apply bounds_mul hx56 hx60 <;> norm_num
  let x62 : ℝ := x53+x61
  have hx62 : Bounds (33500344223 / 500000000000) (4187543153 / 62500000000) x62 := by
    apply bounds_add hx53 hx61 <;> norm_num
  let x63 : ℝ := (2 / 1)⁻¹
  have hx63 : Bounds (1 / 2) (1 / 2) x63 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x64 : ℝ := x62*x63
  have hx64 : Bounds (33500344223 / 1000000000000) (4187543153 / 125000000000) x64 := by
    apply bounds_mul hx62 hx63 <;> norm_num
  let x65 : ℝ := x62/(2 / 1)
  have hx65 : Bounds (33500344223 / 1000000000000) (4187543153 / 125000000000) x65 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx64
  let x66 : ℝ := -x65
  have hx66 : Bounds (-4187543153 / 125000000000) (-33500344223 / 1000000000000) x66 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx65
  let x67 : ℝ := x49+x66
  have hx67 : Bounds (82455854347 / 125000000000) (659646836777 / 1000000000000) x67 := by
    apply bounds_add hx49 hx66 <;> norm_num
  let x68 : ℝ := x49-x65
  have hx68 : Bounds (82455854347 / 125000000000) (659646836777 / 1000000000000) x68 := by
    exact hx67
  let x69 : ℝ := biasE (257389 / 1000000)
  have hx69 : Bounds (82455854347 / 125000000000) (659646836777 / 1000000000000) x69 := by
    simpa +zetaDelta only [biasE, div_one] using hx68
  let x70 : ℝ := Real.log (2 / 1)
  have hx70 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x70 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x71 : ℝ := (1 / 1)+(64453 / 250000)
  have hx71 : Bounds (314453 / 250000) (314453 / 250000) x71 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((64453 / 250000) : ℝ)) <;> norm_num
  let x72 : ℝ := (1 / 1)+(64453 / 250000)
  have hx72 : Bounds (314453 / 250000) (314453 / 250000) x72 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((64453 / 250000) : ℝ)) <;> norm_num
  let x73 : ℝ := Real.log x72
  have hx73 : Bounds (229373703 / 1000000000) (28671713 / 125000000) x73 := by
    exact bounds_log hx72 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x74 : ℝ := x71*x73
  have hx74 : Bounds (288508996117 / 1000000000000) (1126988271 / 3906250000) x74 := by
    apply bounds_mul hx71 hx73 <;> norm_num
  let x75 : ℝ := -(64453 / 250000)
  have hx75 : Bounds (-64453 / 250000) (-64453 / 250000) x75 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((64453 / 250000) : ℝ))
  let x76 : ℝ := (1 / 1)+x75
  have hx76 : Bounds (185547 / 250000) (185547 / 250000) x76 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx75 <;> norm_num
  let x77 : ℝ := (1 / 1)-(64453 / 250000)
  have hx77 : Bounds (185547 / 250000) (185547 / 250000) x77 := by
    exact hx76
  let x78 : ℝ := -(64453 / 250000)
  have hx78 : Bounds (-64453 / 250000) (-64453 / 250000) x78 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((64453 / 250000) : ℝ))
  let x79 : ℝ := (1 / 1)+x78
  have hx79 : Bounds (185547 / 250000) (185547 / 250000) x79 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx78 <;> norm_num
  let x80 : ℝ := (1 / 1)-(64453 / 250000)
  have hx80 : Bounds (185547 / 250000) (185547 / 250000) x80 := by
    exact hx79
  let x81 : ℝ := Real.log x80
  have hx81 : Bounds (-298152699 / 1000000000) (-149076349 / 500000000) x81 := by
    exact bounds_log hx80 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x82 : ℝ := x77*x81
  have hx82 : Bounds (-110642677683 / 500000000000) (-221285354623 / 1000000000000) x82 := by
    apply bounds_mul hx77 hx81 <;> norm_num
  let x83 : ℝ := x74+x82
  have hx83 : Bounds (67223640751 / 1000000000000) (67223642753 / 1000000000000) x83 := by
    apply bounds_add hx74 hx82 <;> norm_num
  let x84 : ℝ := (2 / 1)⁻¹
  have hx84 : Bounds (1 / 2) (1 / 2) x84 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x85 : ℝ := x83*x84
  have hx85 : Bounds (268894563 / 8000000000) (33611821377 / 1000000000000) x85 := by
    apply bounds_mul hx83 hx84 <;> norm_num
  let x86 : ℝ := x83/(2 / 1)
  have hx86 : Bounds (268894563 / 8000000000) (33611821377 / 1000000000000) x86 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx85
  let x87 : ℝ := -x86
  have hx87 : Bounds (-33611821377 / 1000000000000) (-268894563 / 8000000000) x87 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx86
  let x88 : ℝ := x70+x87
  have hx88 : Bounds (659535358623 / 1000000000000) (1055256577 / 1600000000) x88 := by
    apply bounds_add hx70 hx87 <;> norm_num
  let x89 : ℝ := x70-x86
  have hx89 : Bounds (659535358623 / 1000000000000) (1055256577 / 1600000000) x89 := by
    exact hx88
  let x90 : ℝ := biasE (64453 / 250000)
  have hx90 : Bounds (659535358623 / 1000000000000) (1055256577 / 1600000000) x90 := by
    simpa +zetaDelta only [biasE, div_one] using hx89
  let y : ℝ := doubleCapHighTailY x
  have hEll' : Real.log 2 * doubleCapHighTailFloor x = x48 := by
    simpa +zetaDelta only [div_one] using hEll
  have hy : Bounds (257389 / 1000000) (64453 / 250000) y := by
    dsimp only [y, doubleCapHighTailY]
    apply entropyInverseBias_bracket hh0.le hh1.le
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (64453 / 250000) ≤ (1055256577 / 1600000000) := hx90.2
      have h2 : (329767707217 / 500000000000) ≤ x48 := hx48.1
      linarith [hEll']
    · have h1 : x48 ≤ (131929315047 / 200000000000) := hx48.2
      have h2 : (82455854347 / 125000000000) ≤ biasE (257389 / 1000000) := hx69.1
      linarith [hEll']
  let x91 : ℝ := x⁻¹
  have hx91 : Bounds (551724137931 / 100000000000) (2763086886131 / 500000000000) x91 := by
    apply bounds_inv hx <;> norm_num
  let x92 : ℝ := x48*x91
  have hx92 : Bounds (727763215927 / 200000000000) (3645321603027 / 1000000000000) x92 := by
    apply bounds_mul hx48 hx91 <;> norm_num
  let x93 : ℝ := x48/x
  have hx93 : Bounds (727763215927 / 200000000000) (3645321603027 / 1000000000000) x93 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx92
  let x94 : ℝ := Real.log (2 / 1)
  have hx94 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x94 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x95 : ℝ := (1 / 1)+(46351 / 250000)
  have hx95 : Bounds (296351 / 250000) (296351 / 250000) x95 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((46351 / 250000) : ℝ)) <;> norm_num
  let x96 : ℝ := (1 / 1)+(46351 / 250000)
  have hx96 : Bounds (296351 / 250000) (296351 / 250000) x96 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((46351 / 250000) : ℝ)) <;> norm_num
  let x97 : ℝ := Real.log x96
  have hx97 : Bounds (42520911 / 250000000) (34016729 / 200000000) x97 := by
    exact bounds_log hx96 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x98 : ℝ := x95*x97
  have hx98 : Bounds (50404457983 / 250000000000) (100808916559 / 500000000000) x98 := by
    apply bounds_mul hx95 hx97 <;> norm_num
  let x99 : ℝ := -(46351 / 250000)
  have hx99 : Bounds (-46351 / 250000) (-46351 / 250000) x99 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((46351 / 250000) : ℝ))
  let x100 : ℝ := (1 / 1)+x99
  have hx100 : Bounds (203649 / 250000) (203649 / 250000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx99 <;> norm_num
  let x101 : ℝ := (1 / 1)-(46351 / 250000)
  have hx101 : Bounds (203649 / 250000) (203649 / 250000) x101 := by
    exact hx100
  let x102 : ℝ := -(46351 / 250000)
  have hx102 : Bounds (-46351 / 250000) (-46351 / 250000) x102 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((46351 / 250000) : ℝ))
  let x103 : ℝ := (1 / 1)+x102
  have hx103 : Bounds (203649 / 250000) (203649 / 250000) x103 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx102 <;> norm_num
  let x104 : ℝ := (1 / 1)-(46351 / 250000)
  have hx104 : Bounds (203649 / 250000) (203649 / 250000) x104 := by
    exact hx103
  let x105 : ℝ := Real.log x104
  have hx105 : Bounds (-41012599 / 200000000) (-102531497 / 500000000) x105 := by
    exact bounds_log hx104 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x106 : ℝ := x101*x105
  have hx106 : Bounds (-41760873869 / 250000000000) (-8352174733 / 50000000000) x106 := by
    apply bounds_mul hx101 hx105 <;> norm_num
  let x107 : ℝ := x98+x106
  have hx107 : Bounds (4321792057 / 125000000000) (17287169229 / 500000000000) x107 := by
    apply bounds_add hx98 hx106 <;> norm_num
  let x108 : ℝ := (2 / 1)⁻¹
  have hx108 : Bounds (1 / 2) (1 / 2) x108 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x109 : ℝ := x107*x108
  have hx109 : Bounds (4321792057 / 250000000000) (17287169229 / 1000000000000) x109 := by
    apply bounds_mul hx107 hx108 <;> norm_num
  let x110 : ℝ := x107/(2 / 1)
  have hx110 : Bounds (4321792057 / 250000000000) (17287169229 / 1000000000000) x110 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx109
  let x111 : ℝ := -x110
  have hx111 : Bounds (-17287169229 / 1000000000000) (-4321792057 / 250000000000) x111 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx110
  let x112 : ℝ := x94+x111
  have hx112 : Bounds (675860010771 / 1000000000000) (168965003193 / 250000000000) x112 := by
    apply bounds_add hx94 hx111 <;> norm_num
  let x113 : ℝ := x94-x110
  have hx113 : Bounds (675860010771 / 1000000000000) (168965003193 / 250000000000) x113 := by
    exact hx112
  let x114 : ℝ := biasE (46351 / 250000)
  have hx114 : Bounds (675860010771 / 1000000000000) (168965003193 / 250000000000) x114 := by
    simpa +zetaDelta only [biasE, div_one] using hx113
  let x115 : ℝ := Real.log (2 / 1)
  have hx115 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x115 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x116 : ℝ := (1 / 1)+(4643 / 25000)
  have hx116 : Bounds (29643 / 25000) (29643 / 25000) x116 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((4643 / 25000) : ℝ)) <;> norm_num
  let x117 : ℝ := (1 / 1)+(4643 / 25000)
  have hx117 : Bounds (29643 / 25000) (29643 / 25000) x117 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((4643 / 25000) : ℝ)) <;> norm_num
  let x118 : ℝ := Real.log x117
  have hx118 : Bounds (34070037 / 200000000) (85175093 / 500000000) x118 := by
    exact bounds_log hx117 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x119 : ℝ := x116*x118
  have hx119 : Bounds (100993810679 / 500000000000) (12624226409 / 62500000000) x119 := by
    apply bounds_mul hx116 hx118 <;> norm_num
  let x120 : ℝ := -(4643 / 25000)
  have hx120 : Bounds (-4643 / 25000) (-4643 / 25000) x120 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((4643 / 25000) : ℝ))
  let x121 : ℝ := (1 / 1)+x120
  have hx121 : Bounds (20357 / 25000) (20357 / 25000) x121 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx120 <;> norm_num
  let x122 : ℝ := (1 / 1)-(4643 / 25000)
  have hx122 : Bounds (20357 / 25000) (20357 / 25000) x122 := by
    exact hx121
  let x123 : ℝ := -(4643 / 25000)
  have hx123 : Bounds (-4643 / 25000) (-4643 / 25000) x123 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((4643 / 25000) : ℝ))
  let x124 : ℝ := (1 / 1)+x123
  have hx124 : Bounds (20357 / 25000) (20357 / 25000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx123 <;> norm_num
  let x125 : ℝ := (1 / 1)-(4643 / 25000)
  have hx125 : Bounds (20357 / 25000) (20357 / 25000) x125 := by
    exact hx124
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (-12840687 / 62500000) (-205450991 / 1000000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x127 : ℝ := x122*x126
  have hx127 : Bounds (-83647316883 / 500000000000) (-167294632951 / 1000000000000) x127 := by
    apply bounds_mul hx122 hx126 <;> norm_num
  let x128 : ℝ := x119+x127
  have hx128 : Bounds (4336623449 / 125000000000) (34692989593 / 1000000000000) x128 := by
    apply bounds_add hx119 hx127 <;> norm_num
  let x129 : ℝ := (2 / 1)⁻¹
  have hx129 : Bounds (1 / 2) (1 / 2) x129 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x130 : ℝ := x128*x129
  have hx130 : Bounds (4336623449 / 250000000000) (17346494797 / 1000000000000) x130 := by
    apply bounds_mul hx128 hx129 <;> norm_num
  let x131 : ℝ := x128/(2 / 1)
  have hx131 : Bounds (4336623449 / 250000000000) (17346494797 / 1000000000000) x131 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx130
  let x132 : ℝ := -x131
  have hx132 : Bounds (-17346494797 / 1000000000000) (-4336623449 / 250000000000) x132 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx131
  let x133 : ℝ := x115+x132
  have hx133 : Bounds (675800685203 / 1000000000000) (168950171801 / 250000000000) x133 := by
    apply bounds_add hx115 hx132 <;> norm_num
  let x134 : ℝ := x115-x131
  have hx134 : Bounds (675800685203 / 1000000000000) (168950171801 / 250000000000) x134 := by
    exact hx133
  let x135 : ℝ := biasE (4643 / 25000)
  have hx135 : Bounds (675800685203 / 1000000000000) (168950171801 / 250000000000) x135 := by
    simpa +zetaDelta only [biasE, div_one] using hx134
  let x136 : ℝ := x93*(46351 / 250000)
  have hx136 : Bounds (168662764107 / 250000000000) (84482150811 / 125000000000) x136 := by
    apply bounds_mul hx93 (bounds_const ((46351 / 250000) : ℝ)) <;> norm_num
  let x137 : ℝ := x93*(4643 / 25000)
  have hx137 : Bounds (675800922309 / 1000000000000) (135401825623 / 200000000000) x137 := by
    apply bounds_mul hx93 (bounds_const ((4643 / 25000) : ℝ)) <;> norm_num
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
  have hc : Bounds (46351 / 250000) (4643 / 25000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num)
      (by norm_num) (show 0 < x93 by linarith [hx93.1]) hcEq
    · have h1 : x93 * (46351 / 250000) ≤ (84482150811 / 125000000000) := hx136.2
      have h2 : (675860010771 / 1000000000000) ≤ biasE (46351 / 250000) := hx114.1
      linarith
    · have h1 : biasE (4643 / 25000) ≤ (168950171801 / 250000000000) := hx135.2
      have h2 : (675800922309 / 1000000000000) ≤ x93 * (4643 / 25000) := hx137.1
      linarith
  let x138 : ℝ := (1 / 1)+x0
  have hx138 : Bounds (6973 / 5120) (109 / 80) x138 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx0 <;> norm_num
  let x139 : ℝ := -x0
  have hx139 : Bounds (-29 / 80) (-1853 / 5120) x139 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x140 : ℝ := (1 / 1)+x139
  have hx140 : Bounds (51 / 80) (3267 / 5120) x140 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx139 <;> norm_num
  let x141 : ℝ := (1 / 1)-x0
  have hx141 : Bounds (51 / 80) (3267 / 5120) x141 := by
    exact hx140
  let x142 : ℝ := x141⁻¹
  have hx142 : Bounds (391796755433 / 250000000000) (1568627450981 / 1000000000000) x142 := by
    apply bounds_inv hx141 <;> norm_num
  let x143 : ℝ := x138*x142
  have hx143 : Bounds (266796755433 / 125000000000) (1068627450981 / 500000000000) x143 := by
    apply bounds_mul hx138 hx142 <;> norm_num
  let x144 : ℝ := x138/x141
  have hx144 : Bounds (266796755433 / 125000000000) (1068627450981 / 500000000000) x144 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx143
  let x145 : ℝ := Real.log x144
  have hx145 : Bounds (151634683 / 200000000) (3038089 / 4000000) x145 := by
    exact bounds_log hx144 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_14.2)
  let x146 : ℝ := (2 / 1)⁻¹
  have hx146 : Bounds (1 / 2) (1 / 2) x146 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x147 : ℝ := x145*x146
  have hx147 : Bounds (151634683 / 400000000) (3038089 / 8000000) x147 := by
    apply bounds_mul hx145 hx146 <;> norm_num
  let x148 : ℝ := x145/(2 / 1)
  have hx148 : Bounds (151634683 / 400000000) (3038089 / 8000000) x148 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx147
  let x149 : ℝ := (1 / 1)+y
  have hx149 : Bounds (1257389 / 1000000) (314453 / 250000) x149 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x150 : ℝ := -y
  have hx150 : Bounds (-64453 / 250000) (-257389 / 1000000) x150 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x151 : ℝ := (1 / 1)+x150
  have hx151 : Bounds (185547 / 250000) (742611 / 1000000) x151 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx150 <;> norm_num
  let x152 : ℝ := (1 / 1)-y
  have hx152 : Bounds (185547 / 250000) (742611 / 1000000) x152 := by
    exact hx151
  let x153 : ℝ := x152⁻¹
  have hx153 : Bounds (42081251153 / 31250000000) (1347367513353 / 1000000000000) x153 := by
    apply bounds_inv hx152 <;> norm_num
  let x154 : ℝ := x149*x153
  have hx154 : Bounds (26456251153 / 15625000000) (847367513353 / 500000000000) x154 := by
    apply bounds_mul hx149 hx153 <;> norm_num
  let x155 : ℝ := x149/x152
  have hx155 : Bounds (26456251153 / 15625000000) (847367513353 / 500000000000) x155 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx154
  let x156 : ℝ := Real.log x155
  have hx156 : Bounds (526620273 / 1000000000) (527526403 / 1000000000) x156 := by
    exact bounds_log hx155 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_16.2)
  let x157 : ℝ := (2 / 1)⁻¹
  have hx157 : Bounds (1 / 2) (1 / 2) x157 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x158 : ℝ := x156*x157
  have hx158 : Bounds (526620273 / 2000000000) (527526403 / 2000000000) x158 := by
    apply bounds_mul hx156 hx157 <;> norm_num
  let x159 : ℝ := x156/(2 / 1)
  have hx159 : Bounds (526620273 / 2000000000) (527526403 / 2000000000) x159 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx158
  let x160 : ℝ := (1 / 1)+c
  have hx160 : Bounds (296351 / 250000) (29643 / 25000) x160 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x161 : ℝ := -c
  have hx161 : Bounds (-4643 / 25000) (-46351 / 250000) x161 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x162 : ℝ := (1 / 1)+x161
  have hx162 : Bounds (20357 / 25000) (203649 / 250000) x162 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx161 <;> norm_num
  let x163 : ℝ := (1 / 1)-c
  have hx163 : Bounds (20357 / 25000) (203649 / 250000) x163 := by
    exact hx162
  let x164 : ℝ := x163⁻¹
  have hx164 : Bounds (245520478863 / 200000000000) (19188731149 / 15625000000) x164 := by
    apply bounds_inv hx163 <;> norm_num
  let x165 : ℝ := x160*x164
  have hx165 : Bounds (145520478863 / 100000000000) (11376231149 / 7812500000) x165 := by
    apply bounds_mul hx160 hx164 <;> norm_num
  let x166 : ℝ := x160/x163
  have hx166 : Bounds (145520478863 / 100000000000) (11376231149 / 7812500000) x166 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx165
  let x167 : ℝ := Real.log x166
  have hx167 : Bounds (187573319 / 500000000) (375801177 / 1000000000) x167 := by
    exact bounds_log hx166 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x168 : ℝ := (2 / 1)⁻¹
  have hx168 : Bounds (1 / 2) (1 / 2) x168 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x169 : ℝ := x167*x168
  have hx169 : Bounds (187573319 / 1000000000) (375801177 / 2000000000) x169 := by
    apply bounds_mul hx167 hx168 <;> norm_num
  let x170 : ℝ := x167/(2 / 1)
  have hx170 : Bounds (187573319 / 1000000000) (375801177 / 2000000000) x170 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx169
  let x171 : ℝ := Real.log (2 / 1)
  have hx171 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x171 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x172 : ℝ := c*c
  have hx172 : Bounds (2148415201 / 62500000000) (21557449 / 625000000) x172 := by
    apply bounds_mul hc hc <;> norm_num
  let x173 : ℝ := -x172
  have hx173 : Bounds (-21557449 / 625000000) (-2148415201 / 62500000000) x173 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx172
  let x174 : ℝ := (1 / 1)+x173
  have hx174 : Bounds (603442551 / 625000000) (60351584799 / 62500000000) x174 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx173 <;> norm_num
  let x175 : ℝ := (1 / 1)-x172
  have hx175 : Bounds (603442551 / 625000000) (60351584799 / 62500000000) x175 := by
    exact hx174
  let x176 : ℝ := Real.log x175
  have hx176 : Bounds (-35100807 / 1000000000) (-34979349 / 1000000000) x176 := by
    exact bounds_log hx175 (by norm_num) (by simpa only [div_one] using reflection_log_19.1) (by simpa only [div_one] using reflection_log_20.2)
  let x177 : ℝ := (2 / 1)⁻¹
  have hx177 : Bounds (1 / 2) (1 / 2) x177 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x178 : ℝ := x176*x177
  have hx178 : Bounds (-35100807 / 2000000000) (-34979349 / 2000000000) x178 := by
    apply bounds_mul hx176 hx177 <;> norm_num
  let x179 : ℝ := x176/(2 / 1)
  have hx179 : Bounds (-35100807 / 2000000000) (-34979349 / 2000000000) x179 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx178
  let x180 : ℝ := -x179
  have hx180 : Bounds (34979349 / 2000000000) (35100807 / 2000000000) x180 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx179
  let x181 : ℝ := x171+x180
  have hx181 : Bounds (1421273709 / 2000000000) (1421395169 / 2000000000) x181 := by
    apply bounds_add hx171 hx180 <;> norm_num
  let x182 : ℝ := x171-x179
  have hx182 : Bounds (1421273709 / 2000000000) (1421395169 / 2000000000) x182 := by
    exact hx181
  let x183 : ℝ := Real.log (2 / 1)
  have hx183 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x183 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x184 : ℝ := (1 / 1)+(4643 / 25000)
  have hx184 : Bounds (29643 / 25000) (29643 / 25000) x184 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((4643 / 25000) : ℝ)) <;> norm_num
  let x185 : ℝ := (1 / 1)+(4643 / 25000)
  have hx185 : Bounds (29643 / 25000) (29643 / 25000) x185 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((4643 / 25000) : ℝ)) <;> norm_num
  let x186 : ℝ := Real.log x185
  have hx186 : Bounds (34070037 / 200000000) (85175093 / 500000000) x186 := by
    exact bounds_log hx185 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x187 : ℝ := x184*x186
  have hx187 : Bounds (100993810679 / 500000000000) (12624226409 / 62500000000) x187 := by
    apply bounds_mul hx184 hx186 <;> norm_num
  let x188 : ℝ := -(4643 / 25000)
  have hx188 : Bounds (-4643 / 25000) (-4643 / 25000) x188 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((4643 / 25000) : ℝ))
  let x189 : ℝ := (1 / 1)+x188
  have hx189 : Bounds (20357 / 25000) (20357 / 25000) x189 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx188 <;> norm_num
  let x190 : ℝ := (1 / 1)-(4643 / 25000)
  have hx190 : Bounds (20357 / 25000) (20357 / 25000) x190 := by
    exact hx189
  let x191 : ℝ := -(4643 / 25000)
  have hx191 : Bounds (-4643 / 25000) (-4643 / 25000) x191 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((4643 / 25000) : ℝ))
  let x192 : ℝ := (1 / 1)+x191
  have hx192 : Bounds (20357 / 25000) (20357 / 25000) x192 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx191 <;> norm_num
  let x193 : ℝ := (1 / 1)-(4643 / 25000)
  have hx193 : Bounds (20357 / 25000) (20357 / 25000) x193 := by
    exact hx192
  let x194 : ℝ := Real.log x193
  have hx194 : Bounds (-12840687 / 62500000) (-205450991 / 1000000000) x194 := by
    exact bounds_log hx193 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x195 : ℝ := x190*x194
  have hx195 : Bounds (-83647316883 / 500000000000) (-167294632951 / 1000000000000) x195 := by
    apply bounds_mul hx190 hx194 <;> norm_num
  let x196 : ℝ := x187+x195
  have hx196 : Bounds (4336623449 / 125000000000) (34692989593 / 1000000000000) x196 := by
    apply bounds_add hx187 hx195 <;> norm_num
  let x197 : ℝ := (2 / 1)⁻¹
  have hx197 : Bounds (1 / 2) (1 / 2) x197 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x198 : ℝ := x196*x197
  have hx198 : Bounds (4336623449 / 250000000000) (17346494797 / 1000000000000) x198 := by
    apply bounds_mul hx196 hx197 <;> norm_num
  let x199 : ℝ := x196/(2 / 1)
  have hx199 : Bounds (4336623449 / 250000000000) (17346494797 / 1000000000000) x199 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx198
  let x200 : ℝ := -x199
  have hx200 : Bounds (-17346494797 / 1000000000000) (-4336623449 / 250000000000) x200 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx199
  let x201 : ℝ := x183+x200
  have hx201 : Bounds (675800685203 / 1000000000000) (168950171801 / 250000000000) x201 := by
    apply bounds_add hx183 hx200 <;> norm_num
  let x202 : ℝ := x183-x199
  have hx202 : Bounds (675800685203 / 1000000000000) (168950171801 / 250000000000) x202 := by
    exact hx201
  let x203 : ℝ := biasE (4643 / 25000)
  have hx203 : Bounds (675800685203 / 1000000000000) (168950171801 / 250000000000) x203 := by
    simpa +zetaDelta only [biasE, div_one] using hx202
  let x204 : ℝ := Real.log (2 / 1)
  have hx204 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x204 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x205 : ℝ := (1 / 1)+(46351 / 250000)
  have hx205 : Bounds (296351 / 250000) (296351 / 250000) x205 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((46351 / 250000) : ℝ)) <;> norm_num
  let x206 : ℝ := (1 / 1)+(46351 / 250000)
  have hx206 : Bounds (296351 / 250000) (296351 / 250000) x206 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((46351 / 250000) : ℝ)) <;> norm_num
  let x207 : ℝ := Real.log x206
  have hx207 : Bounds (42520911 / 250000000) (34016729 / 200000000) x207 := by
    exact bounds_log hx206 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x208 : ℝ := x205*x207
  have hx208 : Bounds (50404457983 / 250000000000) (100808916559 / 500000000000) x208 := by
    apply bounds_mul hx205 hx207 <;> norm_num
  let x209 : ℝ := -(46351 / 250000)
  have hx209 : Bounds (-46351 / 250000) (-46351 / 250000) x209 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((46351 / 250000) : ℝ))
  let x210 : ℝ := (1 / 1)+x209
  have hx210 : Bounds (203649 / 250000) (203649 / 250000) x210 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx209 <;> norm_num
  let x211 : ℝ := (1 / 1)-(46351 / 250000)
  have hx211 : Bounds (203649 / 250000) (203649 / 250000) x211 := by
    exact hx210
  let x212 : ℝ := -(46351 / 250000)
  have hx212 : Bounds (-46351 / 250000) (-46351 / 250000) x212 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((46351 / 250000) : ℝ))
  let x213 : ℝ := (1 / 1)+x212
  have hx213 : Bounds (203649 / 250000) (203649 / 250000) x213 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx212 <;> norm_num
  let x214 : ℝ := (1 / 1)-(46351 / 250000)
  have hx214 : Bounds (203649 / 250000) (203649 / 250000) x214 := by
    exact hx213
  let x215 : ℝ := Real.log x214
  have hx215 : Bounds (-41012599 / 200000000) (-102531497 / 500000000) x215 := by
    exact bounds_log hx214 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x216 : ℝ := x211*x215
  have hx216 : Bounds (-41760873869 / 250000000000) (-8352174733 / 50000000000) x216 := by
    apply bounds_mul hx211 hx215 <;> norm_num
  let x217 : ℝ := x208+x216
  have hx217 : Bounds (4321792057 / 125000000000) (17287169229 / 500000000000) x217 := by
    apply bounds_add hx208 hx216 <;> norm_num
  let x218 : ℝ := (2 / 1)⁻¹
  have hx218 : Bounds (1 / 2) (1 / 2) x218 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x219 : ℝ := x217*x218
  have hx219 : Bounds (4321792057 / 250000000000) (17287169229 / 1000000000000) x219 := by
    apply bounds_mul hx217 hx218 <;> norm_num
  let x220 : ℝ := x217/(2 / 1)
  have hx220 : Bounds (4321792057 / 250000000000) (17287169229 / 1000000000000) x220 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx219
  let x221 : ℝ := -x220
  have hx221 : Bounds (-17287169229 / 1000000000000) (-4321792057 / 250000000000) x221 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx220
  let x222 : ℝ := x204+x221
  have hx222 : Bounds (675860010771 / 1000000000000) (168965003193 / 250000000000) x222 := by
    apply bounds_add hx204 hx221 <;> norm_num
  let x223 : ℝ := x204-x220
  have hx223 : Bounds (675860010771 / 1000000000000) (168965003193 / 250000000000) x223 := by
    exact hx222
  let x224 : ℝ := biasE (46351 / 250000)
  have hx224 : Bounds (675860010771 / 1000000000000) (168965003193 / 250000000000) x224 := by
    simpa +zetaDelta only [biasE, div_one] using hx223
  let x225 : ℝ := biasE c
  have hx225 : Bounds (675800685203 / 1000000000000) (168965003193 / 250000000000) x225 := by
    exact bounds_biasE hc (by norm_num) (by norm_num) hx203.1 hx224.2
  let x226 : ℝ := x159⁻¹
  have hx226 : Bounds (1895639714549 / 500000000000) (949450725001 / 250000000000) x226 := by
    apply bounds_inv hx159 <;> norm_num
  let x227 : ℝ := x148*x226
  have hx227 : Bounds (1437223635989 / 1000000000000) (721128950917 / 500000000000) x227 := by
    apply bounds_mul hx148 hx226 <;> norm_num
  let x228 : ℝ := x148/x159
  have hx228 : Bounds (1437223635989 / 1000000000000) (721128950917 / 500000000000) x228 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx227
  let x229 : ℝ := c*x148
  have hx229 : Bounds (70284191917 / 1000000000000) (14105847227 / 200000000000) x229 := by
    apply bounds_mul hc hx148 <;> norm_num
  let x230 : ℝ := x225+x229
  have hx230 : Bounds (2331515241 / 3125000000) (746389248907 / 1000000000000) x230 := by
    apply bounds_add hx225 hx229 <;> norm_num
  let x231 : ℝ := x*x170
  have hx231 : Bounds (33942710947 / 1000000000000) (17028490833 / 500000000000) x231 := by
    apply bounds_mul hx hx170 <;> norm_num
  let x232 : ℝ := x48+x231
  have hx232 : Bounds (693478125381 / 1000000000000) (693703556901 / 1000000000000) x232 := by
    apply bounds_add hx48 hx231 <;> norm_num
  let x233 : ℝ := x232⁻¹
  have hx233 : Bounds (144153794521 / 100000000000) (721003275663 / 500000000000) x233 := by
    apply bounds_inv hx232 <;> norm_num
  let x234 : ℝ := x230*x233
  have hx234 : Bounds (215101932143 / 200000000000) (269074546691 / 250000000000) x234 := by
    apply bounds_mul hx230 hx233 <;> norm_num
  let x235 : ℝ := x230/x232
  have hx235 : Bounds (215101932143 / 200000000000) (269074546691 / 250000000000) x235 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx234
  let x236 : ℝ := y*y
  have hx236 : Bounds (66249097321 / 1000000000000) (4154189209 / 62500000000) x236 := by
    apply bounds_mul hy hy <;> norm_num
  let x237 : ℝ := -x236
  have hx237 : Bounds (-4154189209 / 62500000000) (-66249097321 / 1000000000000) x237 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx236
  let x238 : ℝ := (1 / 1)+x237
  have hx238 : Bounds (58345810791 / 62500000000) (933750902679 / 1000000000000) x238 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx237 <;> norm_num
  let x239 : ℝ := (1 / 1)-x236
  have hx239 : Bounds (58345810791 / 62500000000) (933750902679 / 1000000000000) x239 := by
    exact hx238
  let x240 : ℝ := x239*x159
  have hx240 : Bounds (245808694457 / 1000000000000) (49257825499 / 200000000000) x240 := by
    apply bounds_mul hx239 hx159 <;> norm_num
  let x241 : ℝ := c*c
  have hx241 : Bounds (2148415201 / 62500000000) (21557449 / 625000000) x241 := by
    apply bounds_mul hc hc <;> norm_num
  let x242 : ℝ := -x241
  have hx242 : Bounds (-21557449 / 625000000) (-2148415201 / 62500000000) x242 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx241
  let x243 : ℝ := (1 / 1)+x242
  have hx243 : Bounds (603442551 / 625000000) (60351584799 / 62500000000) x243 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx242 <;> norm_num
  let x244 : ℝ := (1 / 1)-x241
  have hx244 : Bounds (603442551 / 625000000) (60351584799 / 62500000000) x244 := by
    exact hx243
  let x245 : ℝ := x244*x182
  have hx245 : Bounds (343062813051 / 500000000000) (686267608599 / 1000000000000) x245 := by
    apply bounds_mul hx244 hx182 <;> norm_num
  let x246 : ℝ := y*y
  have hx246 : Bounds (66249097321 / 1000000000000) (4154189209 / 62500000000) x246 := by
    apply bounds_mul hy hy <;> norm_num
  let x247 : ℝ := (1 / 1)+x246
  have hx247 : Bounds (1066249097321 / 1000000000000) (66654189209 / 62500000000) x247 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx246 <;> norm_num
  let x248 : ℝ := x247*x159
  have hx248 : Bounds (140377097679 / 500000000000) (281294757427 / 1000000000000) x248 := by
    apply bounds_mul hx247 hx159 <;> norm_num
  let x249 : ℝ := -y
  have hx249 : Bounds (-64453 / 250000) (-257389 / 1000000) x249 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x250 : ℝ := x248+x249
  have hx250 : Bounds (11471097679 / 500000000000) (23905757427 / 1000000000000) x250 := by
    apply bounds_add hx248 hx249 <;> norm_num
  let x251 : ℝ := x248-y
  have hx251 : Bounds (11471097679 / 500000000000) (23905757427 / 1000000000000) x251 := by
    exact hx250
  let x252 : ℝ := x240*x240
  have hx252 : Bounds (6042191427 / 100000000000) (60658334323 / 1000000000000) x252 := by
    apply bounds_mul hx240 hx240 <;> norm_num
  let x253 : ℝ := x252⁻¹
  have hx253 : Bounds (8242890372451 / 500000000000) (8275143315813 / 500000000000) x253 := by
    apply bounds_inv hx252 <;> norm_num
  let x254 : ℝ := x251*x253
  have hx254 : Bounds (189110001239 / 500000000000) (395647137563 / 1000000000000) x254 := by
    apply bounds_mul hx251 hx253 <;> norm_num
  let x255 : ℝ := x251/x252
  have hx255 : Bounds (189110001239 / 500000000000) (395647137563 / 1000000000000) x255 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx254
  let x256 : ℝ := (-2 / 1)*x255
  have hx256 : Bounds (-395647137563 / 500000000000) (-189110001239 / 250000000000) x256 := by
    apply bounds_mul (bounds_const ((-2 / 1) : ℝ)) hx255 <;> norm_num
  let x257 : ℝ := x256*x228
  have hx257 : Bounds (-1141250420977 / 1000000000000) (-108717345433 / 100000000000) x257 := by
    apply bounds_mul hx256 hx228 <;> norm_num
  let x258 : ℝ := (2 / 1)*x182
  have hx258 : Bounds (1421273709 / 1000000000) (1421395169 / 1000000000) x258 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx182 <;> norm_num
  let x259 : ℝ := c*c
  have hx259 : Bounds (2148415201 / 62500000000) (21557449 / 625000000) x259 := by
    apply bounds_mul hc hc <;> norm_num
  let x260 : ℝ := -x259
  have hx260 : Bounds (-21557449 / 625000000) (-2148415201 / 62500000000) x260 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx259
  let x261 : ℝ := x258+x260
  have hx261 : Bounds (6933908953 / 5000000000) (173377565723 / 125000000000) x261 := by
    apply bounds_add hx258 hx260 <;> norm_num
  let x262 : ℝ := x258-x259
  have hx262 : Bounds (6933908953 / 5000000000) (173377565723 / 125000000000) x262 := by
    exact hx261
  let x263 : ℝ := c*x262
  have hx263 : Bounds (8034840347 / 31250000000) (257597452049 / 1000000000000) x263 := by
    apply bounds_mul hc hx262 <;> norm_num
  let x264 : ℝ := x245*x245
  have hx264 : Bounds (470768374793 / 1000000000000) (470963230613 / 1000000000000) x264 := by
    apply bounds_mul hx245 hx245 <;> norm_num
  let x265 : ℝ := x264⁻¹
  have hx265 : Bounds (42466160201 / 20000000000) (53104671721 / 25000000000) x265 := by
    apply bounds_inv hx264 <;> norm_num
  let x266 : ℝ := x263*x265
  have hx266 : Bounds (68241763473 / 125000000000) (54718512509 / 100000000000) x266 := by
    apply bounds_mul hx263 hx265 <;> norm_num
  let x267 : ℝ := x263/x264
  have hx267 : Bounds (68241763473 / 125000000000) (54718512509 / 100000000000) x267 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx266
  let x268 : ℝ := (2 / 1)*x267
  have hx268 : Bounds (68241763473 / 62500000000) (54718512509 / 50000000000) x268 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx267 <;> norm_num
  let x269 : ℝ := x268*x235
  have hx269 : Bounds (1174314814071 / 1000000000000) (588934357959 / 500000000000) x269 := by
    apply bounds_mul hx268 hx235 <;> norm_num
  let x270 : ℝ := x257+x269
  have hx270 : Bounds (16532196547 / 500000000000) (22673815397 / 250000000000) x270 := by
    apply bounds_add hx257 hx269 <;> norm_num
  have hPos : 0 < x270 :=
    lt_of_lt_of_le (by norm_num) hx270.1
  have hBridgeL : doubleCapBridgeL x = x48 := by
    exact hEll'
  rw [← doubleCapBridgeDerivativeTraceForm_eq x]
  simpa +zetaDelta only [doubleCapBridgeDerivativeTraceForm,
    hBridgeL, SmallMean.A, biasB, div_one, pow_two] using hPos

theorem acceptedCell : DoubleCapBridgeDerivativeCellCertificate
    (⟨191, by decide⟩ : Fin 256) doubleCapBridgeDerivativeExpression where
  positive x hx := by
    have hloEq : doubleCapBridgeLo (⟨191, by decide⟩ : Fin 256) =
        (1853 / 10240) := by norm_num [doubleCapBridgeLo, doubleCapBridgeStep]
    have hhiEq : doubleCapBridgeHi (⟨191, by decide⟩ : Fin 256) =
        (29 / 160) := by norm_num [doubleCapBridgeHi, doubleCapBridgeStep]
    have hlo : (1853 / 10240) ≤ x := by
      simpa only [hloEq] using hx.1
    have hhi : x ≤ (29 / 160) := by
      simpa only [hhiEq] using hx.2
    exact cell_derivative_pos x ⟨hlo, hhi⟩

#print axioms cell_derivative_pos
#print axioms acceptedCell

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell191

end


