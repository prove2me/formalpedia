-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell082Logs__6
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell082Logs__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T17:25:35.215852+00:00
-- url     : https://prove2.me/theorems/cd951444-d060-4f67-993f-9ac6a600bfe4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell082Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell083…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell082Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell083Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell084Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell085Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell086Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell087Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell082Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell083Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell084Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell085Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell086Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell087Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell082Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell083Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell084Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell085Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell086Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell087Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell082Logs (+5 modules: GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell083Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell084Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell085Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell086Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell087Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell082Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell082
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (65328007 / 250000000) ≤ -Real.log (5120 / 6649) ∧
    -Real.log (5120 / 6649) ≤ (261312029 / 1000000000) := by
  have h := checkLog_sound (w := (1529 / 11769)) (n := 12)
    (lo := (65328007 / 250000000)) (hi := (261312029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6649 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6649 / 5120) = 1/(5120 / 6649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (65328007 / 250000000) (261312029 / 1000000000) (Real.log (6649 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6649 / 5120) = -Real.log (5120 / 6649) := by
    rw [show ((6649 / 5120) : ℝ) = ((5120 / 6649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (354723723 / 1000000000) ≤ -Real.log (3591 / 5120) ∧
    -Real.log (3591 / 5120) ≤ (88680931 / 250000000) := by
  have h := checkLog_sound (w := (1529 / 8711)) (n := 12)
    (lo := (354723723 / 1000000000)) (hi := (88680931 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3591) = 1/(3591 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-88680931 / 250000000) (-354723723 / 1000000000) (Real.log (3591 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (26086073 / 100000000) ≤ -Real.log (2560 / 3323) ∧
    -Real.log (2560 / 3323) ≤ (260860731 / 1000000000) := by
  have h := checkLog_sound (w := (763 / 5883)) (n := 12)
    (lo := (26086073 / 100000000)) (hi := (260860731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3323 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3323 / 2560) = 1/(2560 / 3323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (26086073 / 100000000) (260860731 / 1000000000) (Real.log (3323 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3323 / 2560) = -Real.log (2560 / 3323) := by
    rw [show ((3323 / 2560) : ℝ) = ((2560 / 3323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (7077773 / 20000000) ≤ -Real.log (1797 / 2560) ∧
    -Real.log (1797 / 2560) ≤ (353888651 / 1000000000) := by
  have h := checkLog_sound (w := (763 / 4357)) (n := 12)
    (lo := (7077773 / 20000000)) (hi := (353888651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1797) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1797) = 1/(1797 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-353888651 / 1000000000) (-7077773 / 20000000) (Real.log (1797 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (19190961 / 100000000) ≤ -Real.log (1000000 / 1211561) ∧
    -Real.log (1000000 / 1211561) ≤ (191909611 / 1000000000) := by
  have h := checkLog_sound (w := (211561 / 2211561)) (n := 12)
    (lo := (19190961 / 100000000)) (hi := (191909611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1211561 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1211561 / 1000000) = 1/(1000000 / 1211561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (19190961 / 100000000) (191909611 / 1000000000) (Real.log (1211561 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1211561 / 1000000) = -Real.log (1000000 / 1211561) := by
    rw [show ((1211561 / 1000000) : ℝ) = ((1000000 / 1211561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (237700237 / 1000000000) ≤ -Real.log (788439 / 1000000) ∧
    -Real.log (788439 / 1000000) ≤ (118850119 / 500000000) := by
  have h := checkLog_sound (w := (211561 / 1788439)) (n := 12)
    (lo := (237700237 / 1000000000)) (hi := (118850119 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 788439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 788439) = 1/(788439 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-118850119 / 500000000) (-237700237 / 1000000000) (Real.log (788439 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (19225621 / 100000000) ≤ -Real.log (1000000 / 1211981) ∧
    -Real.log (1000000 / 1211981) ≤ (192256211 / 1000000000) := by
  have h := checkLog_sound (w := (211981 / 2211981)) (n := 12)
    (lo := (19225621 / 100000000)) (hi := (192256211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1211981 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1211981 / 1000000) = 1/(1000000 / 1211981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (19225621 / 100000000) (192256211 / 1000000000) (Real.log (1211981 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1211981 / 1000000) = -Real.log (1000000 / 1211981) := by
    rw [show ((1211981 / 1000000) : ℝ) = ((1000000 / 1211981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (238233077 / 1000000000) ≤ -Real.log (788019 / 1000000) ∧
    -Real.log (788019 / 1000000) ≤ (119116539 / 500000000) := by
  have h := checkLog_sound (w := (211981 / 1788019)) (n := 12)
    (lo := (238233077 / 1000000000)) (hi := (119116539 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 788019) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 788019) = 1/(788019 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-119116539 / 500000000) (-238233077 / 1000000000) (Real.log (788019 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (141043729 / 1000000000) ≤ -Real.log (40000 / 46059) ∧
    -Real.log (40000 / 46059) ≤ (14104373 / 100000000) := by
  have h := checkLog_sound (w := (6059 / 86059)) (n := 12)
    (lo := (141043729 / 1000000000)) (hi := (14104373 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46059 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(46059 / 40000) = 1/(40000 / 46059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (141043729 / 1000000000) (14104373 / 100000000) (Real.log (46059 / 40000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (46059 / 40000) = -Real.log (40000 / 46059) := by
    rw [show ((46059 / 40000) : ℝ) = ((40000 / 46059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (16425573 / 100000000) ≤ -Real.log (33941 / 40000) ∧
    -Real.log (33941 / 40000) ≤ (164255731 / 1000000000) := by
  have h := checkLog_sound (w := (6059 / 73941)) (n := 12)
    (lo := (16425573 / 100000000)) (hi := (164255731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 33941) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 33941) = 1/(33941 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-164255731 / 1000000000) (-16425573 / 100000000) (Real.log (33941 / 40000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (17663897 / 125000000) ≤ -Real.log (1000000 / 1151783) ∧
    -Real.log (1000000 / 1151783) ≤ (141311177 / 1000000000) := by
  have h := checkLog_sound (w := (151783 / 2151783)) (n := 12)
    (lo := (17663897 / 125000000)) (hi := (141311177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1151783 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1151783 / 1000000) = 1/(1000000 / 1151783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (17663897 / 125000000) (141311177 / 1000000000) (Real.log (1151783 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1151783 / 1000000) = -Real.log (1000000 / 1151783) := by
    rw [show ((1151783 / 1000000) : ℝ) = ((1000000 / 1151783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (164618779 / 1000000000) ≤ -Real.log (848217 / 1000000) ∧
    -Real.log (848217 / 1000000) ≤ (8230939 / 50000000) := by
  have h := checkLog_sound (w := (151783 / 1848217)) (n := 12)
    (lo := (164618779 / 1000000000)) (hi := (8230939 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 848217) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 848217) = 1/(848217 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-8230939 / 50000000) (-164618779 / 1000000000) (Real.log (848217 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (614749381 / 1000000000) ≤ -Real.log (100000000000 / 184919309961) ∧
    -Real.log (100000000000 / 184919309961) ≤ (307374691 / 500000000) := by
  have h := checkLog_sound (w := (84919309961 / 284919309961)) (n := 12)
    (lo := (614749381 / 1000000000)) (hi := (307374691 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((184919309961 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(184919309961 / 100000000000) = 1/(100000000000 / 184919309961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (614749381 / 1000000000) (307374691 / 500000000) (Real.log (184919309961 / 100000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (184919309961 / 100000000000) = -Real.log (100000000000 / 184919309961) := by
    rw [show ((184919309961 / 100000000000) : ℝ) = ((100000000000 / 184919309961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (77004469 / 125000000) ≤ -Real.log (100000000000 / 185157337789) ∧
    -Real.log (100000000000 / 185157337789) ≤ (616035753 / 1000000000) := by
  have h := checkLog_sound (w := (85157337789 / 285157337789)) (n := 12)
    (lo := (77004469 / 125000000)) (hi := (616035753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((185157337789 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(185157337789 / 100000000000) = 1/(100000000000 / 185157337789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (77004469 / 125000000) (616035753 / 1000000000) (Real.log (185157337789 / 100000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (185157337789 / 100000000000) = -Real.log (100000000000 / 185157337789) := by
    rw [show ((185157337789 / 100000000000) : ℝ) = ((100000000000 / 185157337789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (53701231 / 125000000) ≤ -Real.log (500000000000 / 768328938573) ∧
    -Real.log (500000000000 / 768328938573) ≤ (429609849 / 1000000000) := by
  have h := checkLog_sound (w := (268328938573 / 1268328938573)) (n := 12)
    (lo := (53701231 / 125000000)) (hi := (429609849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((768328938573 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(768328938573 / 500000000000) = 1/(500000000000 / 768328938573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (53701231 / 125000000) (429609849 / 1000000000) (Real.log (768328938573 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (768328938573 / 500000000000) = -Real.log (500000000000 / 768328938573) := by
    rw [show ((768328938573 / 500000000000) : ℝ) = ((500000000000 / 768328938573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (53811161 / 125000000) ≤ -Real.log (500000000000 / 769004935161) ∧
    -Real.log (500000000000 / 769004935161) ≤ (430489289 / 1000000000) := by
  have h := checkLog_sound (w := (269004935161 / 1269004935161)) (n := 12)
    (lo := (53811161 / 125000000)) (hi := (430489289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((769004935161 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(769004935161 / 500000000000) = 1/(500000000000 / 769004935161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (53811161 / 125000000) (430489289 / 1000000000) (Real.log (769004935161 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (769004935161 / 500000000000) = -Real.log (500000000000 / 769004935161) := by
    rw [show ((769004935161 / 500000000000) : ℝ) = ((500000000000 / 769004935161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (15264973 / 50000000) ≤ -Real.log (250000000000 / 339257829763) ∧
    -Real.log (250000000000 / 339257829763) ≤ (305299461 / 1000000000) := by
  have h := checkLog_sound (w := (89257829763 / 589257829763)) (n := 12)
    (lo := (15264973 / 50000000)) (hi := (305299461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((339257829763 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(339257829763 / 250000000000) = 1/(250000000000 / 339257829763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (15264973 / 50000000) (305299461 / 1000000000) (Real.log (339257829763 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (339257829763 / 250000000000) = -Real.log (250000000000 / 339257829763) := by
    rw [show ((339257829763 / 250000000000) : ℝ) = ((250000000000 / 339257829763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (76482489 / 250000000) ≤ -Real.log (250000000000 / 339471797901) ∧
    -Real.log (250000000000 / 339471797901) ≤ (305929957 / 1000000000) := by
  have h := checkLog_sound (w := (89471797901 / 589471797901)) (n := 12)
    (lo := (76482489 / 250000000)) (hi := (305929957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((339471797901 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(339471797901 / 250000000000) = 1/(250000000000 / 339471797901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (76482489 / 250000000) (305929957 / 1000000000) (Real.log (339471797901 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (339471797901 / 250000000000) = -Real.log (250000000000 / 339471797901) := by
    rw [show ((339471797901 / 250000000000) : ℝ) = ((250000000000 / 339471797901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (23307603 / 1000000000) ≤ -Real.log (976961920911 / 1000000000000) ∧
    -Real.log (976961920911 / 1000000000000) ≤ (5826901 / 250000000) := by
  have h := checkLog_sound (w := (23038079089 / 1976961920911)) (n := 12)
    (lo := (23307603 / 1000000000)) (hi := (5826901 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 976961920911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 976961920911) = 1/(976961920911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-5826901 / 250000000) (-23307603 / 1000000000) (Real.log (976961920911 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (23212001 / 1000000000) ≤ -Real.log (1563288519 / 1600000000) ∧
    -Real.log (1563288519 / 1600000000) ≤ (11606001 / 500000000) := by
  have h := checkLog_sound (w := (36711481 / 3163288519)) (n := 12)
    (lo := (23212001 / 1000000000)) (hi := (11606001 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1563288519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1563288519) = 1/(1563288519 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-11606001 / 500000000) (-23212001 / 1000000000) (Real.log (1563288519 / 1600000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell082

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell083Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell083
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (130881561 / 500000000) ≤ -Real.log (1280 / 1663) ∧
    -Real.log (1280 / 1663) ≤ (261763123 / 1000000000) := by
  have h := checkLog_sound (w := (383 / 2943)) (n := 12)
    (lo := (130881561 / 500000000)) (hi := (261763123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1663 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1663 / 1280) = 1/(1280 / 1663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (130881561 / 500000000) (261763123 / 1000000000) (Real.log (1663 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1663 / 1280) = -Real.log (1280 / 1663) := by
    rw [show ((1663 / 1280) : ℝ) = ((1280 / 1663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (177779747 / 500000000) ≤ -Real.log (897 / 1280) ∧
    -Real.log (897 / 1280) ≤ (71111899 / 200000000) := by
  have h := checkLog_sound (w := (383 / 2177)) (n := 12)
    (lo := (177779747 / 500000000)) (hi := (71111899 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 897) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 897) = 1/(897 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-71111899 / 200000000) (-177779747 / 500000000) (Real.log (897 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (65328007 / 250000000) ≤ -Real.log (5120 / 6649) ∧
    -Real.log (5120 / 6649) ≤ (261312029 / 1000000000) := by
  have h := checkLog_sound (w := (1529 / 11769)) (n := 12)
    (lo := (65328007 / 250000000)) (hi := (261312029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6649 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6649 / 5120) = 1/(5120 / 6649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (65328007 / 250000000) (261312029 / 1000000000) (Real.log (6649 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6649 / 5120) = -Real.log (5120 / 6649) := by
    rw [show ((6649 / 5120) : ℝ) = ((5120 / 6649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (354723723 / 1000000000) ≤ -Real.log (3591 / 5120) ∧
    -Real.log (3591 / 5120) ≤ (88680931 / 250000000) := by
  have h := checkLog_sound (w := (1529 / 8711)) (n := 12)
    (lo := (354723723 / 1000000000)) (hi := (88680931 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3591) = 1/(3591 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-88680931 / 250000000) (-354723723 / 1000000000) (Real.log (3591 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (38451077 / 200000000) ≤ -Real.log (50000 / 60599) ∧
    -Real.log (50000 / 60599) ≤ (96127693 / 500000000) := by
  have h := checkLog_sound (w := (10599 / 110599)) (n := 12)
    (lo := (38451077 / 200000000)) (hi := (96127693 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60599 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60599 / 50000) = 1/(50000 / 60599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (38451077 / 200000000) (96127693 / 500000000) (Real.log (60599 / 50000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (60599 / 50000) = -Real.log (50000 / 60599) := by
    rw [show ((60599 / 50000) : ℝ) = ((50000 / 60599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (930593 / 3906250) ≤ -Real.log (39401 / 50000) ∧
    -Real.log (39401 / 50000) ≤ (238231809 / 1000000000) := by
  have h := checkLog_sound (w := (10599 / 89401)) (n := 12)
    (lo := (930593 / 3906250)) (hi := (238231809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 39401) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 39401) = 1/(39401 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-238231809 / 1000000000) (-930593 / 3906250) (Real.log (39401 / 50000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (96300933 / 500000000) ≤ -Real.log (2500 / 3031) ∧
    -Real.log (2500 / 3031) ≤ (192601867 / 1000000000) := by
  have h := checkLog_sound (w := (531 / 5531)) (n := 12)
    (lo := (96300933 / 500000000)) (hi := (192601867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3031 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3031 / 2500) = 1/(2500 / 3031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (96300933 / 500000000) (192601867 / 1000000000) (Real.log (3031 / 2500)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3031 / 2500) = -Real.log (2500 / 3031) := by
    rw [show ((3031 / 2500) : ℝ) = ((2500 / 3031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (59691233 / 250000000) ≤ -Real.log (1969 / 2500) ∧
    -Real.log (1969 / 2500) ≤ (238764933 / 1000000000) := by
  have h := checkLog_sound (w := (531 / 4469)) (n := 12)
    (lo := (59691233 / 250000000)) (hi := (238764933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 1969) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 1969) = 1/(1969 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-238764933 / 1000000000) (-59691233 / 250000000) (Real.log (1969 / 2500)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (35327577 / 250000000) ≤ -Real.log (500000 / 575891) ∧
    -Real.log (500000 / 575891) ≤ (141310309 / 1000000000) := by
  have h := checkLog_sound (w := (75891 / 1075891)) (n := 12)
    (lo := (35327577 / 250000000)) (hi := (141310309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((575891 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(575891 / 500000) = 1/(500000 / 575891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (35327577 / 250000000) (141310309 / 1000000000) (Real.log (575891 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (575891 / 500000) = -Real.log (500000 / 575891) := by
    rw [show ((575891 / 500000) : ℝ) = ((500000 / 575891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (51443 / 312500) ≤ -Real.log (424109 / 500000) ∧
    -Real.log (424109 / 500000) ≤ (164617601 / 1000000000) := by
  have h := checkLog_sound (w := (75891 / 924109)) (n := 12)
    (lo := (51443 / 312500)) (hi := (164617601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 424109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 424109) = 1/(424109 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-164617601 / 1000000000) (-51443 / 312500) (Real.log (424109 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (17697319 / 125000000) ≤ -Real.log (1000000 / 1152091) ∧
    -Real.log (1000000 / 1152091) ≤ (141578553 / 1000000000) := by
  have h := checkLog_sound (w := (152091 / 2152091)) (n := 12)
    (lo := (17697319 / 125000000)) (hi := (141578553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1152091 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1152091 / 1000000) = 1/(1000000 / 1152091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (17697319 / 125000000) (141578553 / 1000000000) (Real.log (1152091 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1152091 / 1000000) = -Real.log (1000000 / 1152091) := by
    rw [show ((1152091 / 1000000) : ℝ) = ((1000000 / 1152091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (4124549 / 25000000) ≤ -Real.log (847909 / 1000000) ∧
    -Real.log (847909 / 1000000) ≤ (164981961 / 1000000000) := by
  have h := checkLog_sound (w := (152091 / 1847909)) (n := 12)
    (lo := (4124549 / 25000000)) (hi := (164981961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 847909) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 847909) = 1/(847909 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-164981961 / 1000000000) (-4124549 / 25000000) (Real.log (847909 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (77004469 / 125000000) ≤ -Real.log (31250000000 / 57861668059) ∧
    -Real.log (31250000000 / 57861668059) ≤ (616035753 / 1000000000) := by
  have h := checkLog_sound (w := (26611668059 / 89111668059)) (n := 12)
    (lo := (77004469 / 125000000)) (hi := (616035753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57861668059 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(57861668059 / 31250000000) = 1/(31250000000 / 57861668059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (77004469 / 125000000) (616035753 / 1000000000) (Real.log (57861668059 / 31250000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (57861668059 / 31250000000) = -Real.log (31250000000 / 57861668059) := by
    rw [show ((57861668059 / 31250000000) : ℝ) = ((31250000000 / 57861668059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (617322617 / 1000000000) ≤ -Real.log (125000000000 / 231744704571) ∧
    -Real.log (125000000000 / 231744704571) ≤ (308661309 / 500000000) := by
  have h := checkLog_sound (w := (106744704571 / 356744704571)) (n := 12)
    (lo := (617322617 / 1000000000)) (hi := (308661309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((231744704571 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(231744704571 / 125000000000) = 1/(125000000000 / 231744704571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (617322617 / 1000000000) (308661309 / 500000000) (Real.log (231744704571 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (231744704571 / 125000000000) = -Real.log (125000000000 / 231744704571) := by
    rw [show ((231744704571 / 125000000000) : ℝ) = ((125000000000 / 231744704571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (215243597 / 500000000) ≤ -Real.log (125000000000 / 192250831197) ∧
    -Real.log (125000000000 / 192250831197) ≤ (86097439 / 200000000) := by
  have h := checkLog_sound (w := (67250831197 / 317250831197)) (n := 12)
    (lo := (215243597 / 500000000)) (hi := (86097439 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((192250831197 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(192250831197 / 125000000000) = 1/(125000000000 / 192250831197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (215243597 / 500000000) (86097439 / 200000000) (Real.log (192250831197 / 125000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (192250831197 / 125000000000) = -Real.log (125000000000 / 192250831197) := by
    rw [show ((192250831197 / 125000000000) : ℝ) = ((125000000000 / 192250831197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (215683399 / 500000000) ≤ -Real.log (50000000000 / 76968004063) ∧
    -Real.log (50000000000 / 76968004063) ≤ (431366799 / 1000000000) := by
  have h := checkLog_sound (w := (26968004063 / 126968004063)) (n := 12)
    (lo := (215683399 / 500000000)) (hi := (431366799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76968004063 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76968004063 / 50000000000) = 1/(50000000000 / 76968004063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (215683399 / 500000000) (431366799 / 1000000000) (Real.log (76968004063 / 50000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (76968004063 / 50000000000) = -Real.log (50000000000 / 76968004063) := by
    rw [show ((76968004063 / 50000000000) : ℝ) = ((50000000000 / 76968004063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (305927909 / 1000000000) ≤ -Real.log (100000000000 / 135788441179) ∧
    -Real.log (100000000000 / 135788441179) ≤ (30592791 / 100000000) := by
  have h := checkLog_sound (w := (35788441179 / 235788441179)) (n := 12)
    (lo := (305927909 / 1000000000)) (hi := (30592791 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((135788441179 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(135788441179 / 100000000000) = 1/(100000000000 / 135788441179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (305927909 / 1000000000) (30592791 / 100000000) (Real.log (135788441179 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (135788441179 / 100000000000) = -Real.log (100000000000 / 135788441179) := by
    rw [show ((135788441179 / 100000000000) : ℝ) = ((100000000000 / 135788441179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (598751 / 1953125) ≤ -Real.log (500000000000 / 679371842969) ∧
    -Real.log (500000000000 / 679371842969) ≤ (306560513 / 1000000000) := by
  have h := checkLog_sound (w := (179371842969 / 1179371842969)) (n := 12)
    (lo := (598751 / 1953125)) (hi := (306560513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((679371842969 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(679371842969 / 500000000000) = 1/(500000000000 / 679371842969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (598751 / 1953125) (306560513 / 1000000000) (Real.log (679371842969 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (679371842969 / 500000000000) = -Real.log (500000000000 / 679371842969) := by
    rw [show ((679371842969 / 500000000000) : ℝ) = ((500000000000 / 679371842969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1462713 / 62500000) ≤ -Real.log (976868327719 / 1000000000000) ∧
    -Real.log (976868327719 / 1000000000000) ≤ (23403409 / 1000000000) := by
  have h := checkLog_sound (w := (23131672281 / 1976868327719)) (n := 12)
    (lo := (1462713 / 62500000)) (hi := (23403409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 976868327719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 976868327719) = 1/(976868327719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-23403409 / 1000000000) (-1462713 / 62500000) (Real.log (976868327719 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (5826823 / 250000000) ≤ -Real.log (244240556119 / 250000000000) ∧
    -Real.log (244240556119 / 250000000000) ≤ (23307293 / 1000000000) := by
  have h := checkLog_sound (w := (5759443881 / 494240556119)) (n := 12)
    (lo := (5826823 / 250000000)) (hi := (23307293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244240556119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244240556119) = 1/(244240556119 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-23307293 / 1000000000) (-5826823 / 250000000) (Real.log (244240556119 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell083

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell084Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell084
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (65553503 / 250000000) ≤ -Real.log (1024 / 1331) ∧
    -Real.log (1024 / 1331) ≤ (262214013 / 1000000000) := by
  have h := checkLog_sound (w := (307 / 2355)) (n := 12)
    (lo := (65553503 / 250000000)) (hi := (262214013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1331 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1331 / 1024) = 1/(1024 / 1331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (65553503 / 250000000) (262214013 / 1000000000) (Real.log (1331 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1331 / 1024) = -Real.log (1024 / 1331) := by
    rw [show ((1331 / 1024) : ℝ) = ((1024 / 1331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (89098991 / 250000000) ≤ -Real.log (717 / 1024) ∧
    -Real.log (717 / 1024) ≤ (71279193 / 200000000) := by
  have h := checkLog_sound (w := (307 / 1741)) (n := 12)
    (lo := (89098991 / 250000000)) (hi := (71279193 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 717) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 717) = 1/(717 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-71279193 / 200000000) (-89098991 / 250000000) (Real.log (717 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (130881561 / 500000000) ≤ -Real.log (1280 / 1663) ∧
    -Real.log (1280 / 1663) ≤ (261763123 / 1000000000) := by
  have h := checkLog_sound (w := (383 / 2943)) (n := 12)
    (lo := (130881561 / 500000000)) (hi := (261763123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1663 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1663 / 1280) = 1/(1280 / 1663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (130881561 / 500000000) (261763123 / 1000000000) (Real.log (1663 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1663 / 1280) = -Real.log (1280 / 1663) := by
    rw [show ((1663 / 1280) : ℝ) = ((1280 / 1663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (177779747 / 500000000) ≤ -Real.log (897 / 1280) ∧
    -Real.log (897 / 1280) ≤ (71111899 / 200000000) := by
  have h := checkLog_sound (w := (383 / 2177)) (n := 12)
    (lo := (177779747 / 500000000)) (hi := (71111899 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 897) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 897) = 1/(897 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-71111899 / 200000000) (-177779747 / 500000000) (Real.log (897 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (192601041 / 1000000000) ≤ -Real.log (1000000 / 1212399) ∧
    -Real.log (1000000 / 1212399) ≤ (96300521 / 500000000) := by
  have h := checkLog_sound (w := (212399 / 2212399)) (n := 12)
    (lo := (192601041 / 1000000000)) (hi := (96300521 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1212399 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1212399 / 1000000) = 1/(1000000 / 1212399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (192601041 / 1000000000) (96300521 / 500000000) (Real.log (1212399 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1212399 / 1000000) = -Real.log (1000000 / 1212399) := by
    rw [show ((1212399 / 1000000) : ℝ) = ((1000000 / 1212399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (119381831 / 500000000) ≤ -Real.log (787601 / 1000000) ∧
    -Real.log (787601 / 1000000) ≤ (238763663 / 1000000000) := by
  have h := checkLog_sound (w := (212399 / 1787601)) (n := 12)
    (lo := (119381831 / 500000000)) (hi := (238763663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 787601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 787601) = 1/(787601 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-238763663 / 1000000000) (-119381831 / 500000000) (Real.log (787601 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (96473701 / 500000000) ≤ -Real.log (1000000 / 1212819) ∧
    -Real.log (1000000 / 1212819) ≤ (192947403 / 1000000000) := by
  have h := checkLog_sound (w := (212819 / 2212819)) (n := 12)
    (lo := (96473701 / 500000000)) (hi := (192947403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1212819 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1212819 / 1000000) = 1/(1000000 / 1212819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (96473701 / 500000000) (192947403 / 1000000000) (Real.log (1212819 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1212819 / 1000000) = -Real.log (1000000 / 1212819) := by
    rw [show ((1212819 / 1000000) : ℝ) = ((1000000 / 1212819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (239297069 / 1000000000) ≤ -Real.log (787181 / 1000000) ∧
    -Real.log (787181 / 1000000) ≤ (23929707 / 100000000) := by
  have h := checkLog_sound (w := (212819 / 1787181)) (n := 12)
    (lo := (239297069 / 1000000000)) (hi := (23929707 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 787181) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 787181) = 1/(787181 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-23929707 / 100000000) (-239297069 / 1000000000) (Real.log (787181 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (35394421 / 250000000) ≤ -Real.log (100000 / 115209) ∧
    -Real.log (100000 / 115209) ≤ (28315537 / 200000000) := by
  have h := checkLog_sound (w := (15209 / 215209)) (n := 12)
    (lo := (35394421 / 250000000)) (hi := (28315537 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((115209 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(115209 / 100000) = 1/(100000 / 115209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (35394421 / 250000000) (28315537 / 200000000) (Real.log (115209 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (115209 / 100000) = -Real.log (100000 / 115209) := by
    rw [show ((115209 / 100000) : ℝ) = ((100000 / 115209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (8249039 / 50000000) ≤ -Real.log (84791 / 100000) ∧
    -Real.log (84791 / 100000) ≤ (164980781 / 1000000000) := by
  have h := checkLog_sound (w := (15209 / 184791)) (n := 12)
    (lo := (8249039 / 50000000)) (hi := (164980781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 84791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 84791) = 1/(84791 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-164980781 / 1000000000) (-8249039 / 50000000) (Real.log (84791 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (4432683 / 31250000) ≤ -Real.log (1000000 / 1152399) ∧
    -Real.log (1000000 / 1152399) ≤ (141845857 / 1000000000) := by
  have h := checkLog_sound (w := (152399 / 2152399)) (n := 12)
    (lo := (4432683 / 31250000)) (hi := (141845857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1152399 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1152399 / 1000000) = 1/(1000000 / 1152399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (4432683 / 31250000) (141845857 / 1000000000) (Real.log (1152399 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1152399 / 1000000) = -Real.log (1000000 / 1152399) := by
    rw [show ((1152399 / 1000000) : ℝ) = ((1000000 / 1152399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (20668159 / 125000000) ≤ -Real.log (847601 / 1000000) ∧
    -Real.log (847601 / 1000000) ≤ (165345273 / 1000000000) := by
  have h := checkLog_sound (w := (152399 / 1847601)) (n := 12)
    (lo := (20668159 / 125000000)) (hi := (165345273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 847601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 847601) = 1/(847601 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-165345273 / 1000000000) (-20668159 / 125000000) (Real.log (847601 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (617322617 / 1000000000) ≤ -Real.log (500000000000 / 926978818283) ∧
    -Real.log (500000000000 / 926978818283) ≤ (308661309 / 500000000) := by
  have h := checkLog_sound (w := (426978818283 / 1426978818283)) (n := 12)
    (lo := (617322617 / 1000000000)) (hi := (308661309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((926978818283 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(926978818283 / 500000000000) = 1/(500000000000 / 926978818283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (617322617 / 1000000000) (308661309 / 500000000) (Real.log (926978818283 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (926978818283 / 500000000000) = -Real.log (500000000000 / 926978818283) := by
    rw [show ((926978818283 / 500000000000) : ℝ) = ((500000000000 / 926978818283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (618609977 / 1000000000) ≤ -Real.log (250000000000 / 464086471409) ∧
    -Real.log (250000000000 / 464086471409) ≤ (309304989 / 500000000) := by
  have h := checkLog_sound (w := (214086471409 / 714086471409)) (n := 12)
    (lo := (618609977 / 1000000000)) (hi := (309304989 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((464086471409 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(464086471409 / 250000000000) = 1/(250000000000 / 464086471409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (618609977 / 1000000000) (309304989 / 500000000) (Real.log (464086471409 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (464086471409 / 250000000000) = -Real.log (250000000000 / 464086471409) := by
    rw [show ((464086471409 / 250000000000) : ℝ) = ((250000000000 / 464086471409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (431364703 / 1000000000) ≤ -Real.log (3906250000 / 6013112723) ∧
    -Real.log (3906250000 / 6013112723) ≤ (13480147 / 31250000) := by
  have h := checkLog_sound (w := (2106862723 / 9919362723)) (n := 12)
    (lo := (431364703 / 1000000000)) (hi := (13480147 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6013112723 / 3906250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6013112723 / 3906250000) = 1/(3906250000 / 6013112723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (431364703 / 1000000000) (13480147 / 31250000) (Real.log (6013112723 / 3906250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (6013112723 / 3906250000) = -Real.log (3906250000 / 6013112723) := by
    rw [show ((6013112723 / 3906250000) : ℝ) = ((3906250000 / 6013112723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (432244471 / 1000000000) ≤ -Real.log (500000000000 / 770355864789) ∧
    -Real.log (500000000000 / 770355864789) ≤ (54030559 / 125000000) := by
  have h := checkLog_sound (w := (270355864789 / 1270355864789)) (n := 12)
    (lo := (432244471 / 1000000000)) (hi := (54030559 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((770355864789 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(770355864789 / 500000000000) = 1/(500000000000 / 770355864789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (432244471 / 1000000000) (54030559 / 125000000) (Real.log (770355864789 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (770355864789 / 500000000000) = -Real.log (500000000000 / 770355864789) := by
    rw [show ((770355864789 / 500000000000) : ℝ) = ((500000000000 / 770355864789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (61311693 / 200000000) ≤ -Real.log (125000000000 / 169842613013) ∧
    -Real.log (125000000000 / 169842613013) ≤ (153279233 / 500000000) := by
  have h := checkLog_sound (w := (44842613013 / 294842613013)) (n := 12)
    (lo := (61311693 / 200000000)) (hi := (153279233 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169842613013 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169842613013 / 125000000000) = 1/(125000000000 / 169842613013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (61311693 / 200000000) (153279233 / 500000000) (Real.log (169842613013 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (169842613013 / 125000000000) = -Real.log (125000000000 / 169842613013) := by
    rw [show ((169842613013 / 125000000000) : ℝ) = ((125000000000 / 169842613013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (307191129 / 1000000000) ≤ -Real.log (500000000000 / 679800401369) ∧
    -Real.log (500000000000 / 679800401369) ≤ (30719113 / 100000000) := by
  have h := checkLog_sound (w := (179800401369 / 1179800401369)) (n := 12)
    (lo := (307191129 / 1000000000)) (hi := (30719113 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((679800401369 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(679800401369 / 500000000000) = 1/(500000000000 / 679800401369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (307191129 / 1000000000) (30719113 / 100000000) (Real.log (679800401369 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (679800401369 / 500000000000) = -Real.log (500000000000 / 679800401369) := by
    rw [show ((679800401369 / 500000000000) : ℝ) = ((500000000000 / 679800401369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2937427 / 125000000) ≤ -Real.log (976774544799 / 1000000000000) ∧
    -Real.log (976774544799 / 1000000000000) ≤ (23499417 / 1000000000) := by
  have h := checkLog_sound (w := (23225455201 / 1976774544799)) (n := 12)
    (lo := (2937427 / 125000000)) (hi := (23499417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 976774544799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 976774544799) = 1/(976774544799 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-23499417 / 1000000000) (-2937427 / 125000000) (Real.log (976774544799 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (2925387 / 125000000) ≤ -Real.log (9768686319 / 10000000000) ∧
    -Real.log (9768686319 / 10000000000) ≤ (23403097 / 1000000000) := by
  have h := checkLog_sound (w := (231313681 / 19768686319)) (n := 12)
    (lo := (2925387 / 125000000)) (hi := (23403097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9768686319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9768686319) = 1/(9768686319 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-23403097 / 1000000000) (-2925387 / 125000000) (Real.log (9768686319 / 10000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell084

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell085Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell085
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (2626647 / 10000000) ≤ -Real.log (2560 / 3329) ∧
    -Real.log (2560 / 3329) ≤ (262664701 / 1000000000) := by
  have h := checkLog_sound (w := (769 / 5889)) (n := 12)
    (lo := (2626647 / 10000000)) (hi := (262664701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3329 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3329 / 2560) = 1/(2560 / 3329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (2626647 / 10000000) (262664701 / 1000000000) (Real.log (3329 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3329 / 2560) = -Real.log (2560 / 3329) := by
    rw [show ((3329 / 2560) : ℝ) = ((2560 / 3329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (71446627 / 200000000) ≤ -Real.log (1791 / 2560) ∧
    -Real.log (1791 / 2560) ≤ (22327071 / 62500000) := by
  have h := checkLog_sound (w := (769 / 4351)) (n := 12)
    (lo := (71446627 / 200000000)) (hi := (22327071 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1791) = 1/(1791 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-22327071 / 62500000) (-71446627 / 200000000) (Real.log (1791 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (65553503 / 250000000) ≤ -Real.log (1024 / 1331) ∧
    -Real.log (1024 / 1331) ≤ (262214013 / 1000000000) := by
  have h := checkLog_sound (w := (307 / 2355)) (n := 12)
    (lo := (65553503 / 250000000)) (hi := (262214013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1331 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1331 / 1024) = 1/(1024 / 1331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (65553503 / 250000000) (262214013 / 1000000000) (Real.log (1331 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1331 / 1024) = -Real.log (1024 / 1331) := by
    rw [show ((1331 / 1024) : ℝ) = ((1024 / 1331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (89098991 / 250000000) ≤ -Real.log (717 / 1024) ∧
    -Real.log (717 / 1024) ≤ (71279193 / 200000000) := by
  have h := checkLog_sound (w := (307 / 1741)) (n := 12)
    (lo := (89098991 / 250000000)) (hi := (71279193 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 717) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 717) = 1/(717 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-71279193 / 200000000) (-89098991 / 250000000) (Real.log (717 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (192946577 / 1000000000) ≤ -Real.log (500000 / 606409) ∧
    -Real.log (500000 / 606409) ≤ (96473289 / 500000000) := by
  have h := checkLog_sound (w := (106409 / 1106409)) (n := 12)
    (lo := (192946577 / 1000000000)) (hi := (96473289 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((606409 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(606409 / 500000) = 1/(500000 / 606409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (192946577 / 1000000000) (96473289 / 500000000) (Real.log (606409 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (606409 / 500000) = -Real.log (500000 / 606409) := by
    rw [show ((606409 / 500000) : ℝ) = ((500000 / 606409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (239295799 / 1000000000) ≤ -Real.log (393591 / 500000) ∧
    -Real.log (393591 / 500000) ≤ (1196479 / 5000000) := by
  have h := checkLog_sound (w := (106409 / 893591)) (n := 12)
    (lo := (239295799 / 1000000000)) (hi := (1196479 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 393591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 393591) = 1/(393591 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1196479 / 5000000) (-239295799 / 1000000000) (Real.log (393591 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (96646821 / 500000000) ≤ -Real.log (1000000 / 1213239) ∧
    -Real.log (1000000 / 1213239) ≤ (193293643 / 1000000000) := by
  have h := checkLog_sound (w := (213239 / 2213239)) (n := 12)
    (lo := (96646821 / 500000000)) (hi := (193293643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1213239 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1213239 / 1000000) = 1/(1000000 / 1213239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (96646821 / 500000000) (193293643 / 1000000000) (Real.log (1213239 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1213239 / 1000000) = -Real.log (1000000 / 1213239) := by
    rw [show ((1213239 / 1000000) : ℝ) = ((1000000 / 1213239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (239830761 / 1000000000) ≤ -Real.log (786761 / 1000000) ∧
    -Real.log (786761 / 1000000) ≤ (119915381 / 500000000) := by
  have h := checkLog_sound (w := (213239 / 1786761)) (n := 12)
    (lo := (239830761 / 1000000000)) (hi := (119915381 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 786761) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 786761) = 1/(786761 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-119915381 / 500000000) (-239830761 / 1000000000) (Real.log (786761 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (35461247 / 250000000) ≤ -Real.log (500000 / 576199) ∧
    -Real.log (500000 / 576199) ≤ (141844989 / 1000000000) := by
  have h := checkLog_sound (w := (76199 / 1076199)) (n := 12)
    (lo := (35461247 / 250000000)) (hi := (141844989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((576199 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(576199 / 500000) = 1/(500000 / 576199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (35461247 / 250000000) (141844989 / 1000000000) (Real.log (576199 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (576199 / 500000) = -Real.log (500000 / 576199) := by
    rw [show ((576199 / 500000) : ℝ) = ((500000 / 576199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (41336023 / 250000000) ≤ -Real.log (423801 / 500000) ∧
    -Real.log (423801 / 500000) ≤ (165344093 / 1000000000) := by
  have h := checkLog_sound (w := (76199 / 923801)) (n := 12)
    (lo := (41336023 / 250000000)) (hi := (165344093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 423801) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 423801) = 1/(423801 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-165344093 / 1000000000) (-41336023 / 250000000) (Real.log (423801 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (142113089 / 1000000000) ≤ -Real.log (1000000 / 1152707) ∧
    -Real.log (1000000 / 1152707) ≤ (14211309 / 100000000) := by
  have h := checkLog_sound (w := (152707 / 2152707)) (n := 12)
    (lo := (142113089 / 1000000000)) (hi := (14211309 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1152707 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1152707 / 1000000) = 1/(1000000 / 1152707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (142113089 / 1000000000) (14211309 / 100000000) (Real.log (1152707 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1152707 / 1000000) = -Real.log (1000000 / 1152707) := by
    rw [show ((1152707 / 1000000) : ℝ) = ((1000000 / 1152707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (165708717 / 1000000000) ≤ -Real.log (847293 / 1000000) ∧
    -Real.log (847293 / 1000000) ≤ (82854359 / 500000000) := by
  have h := checkLog_sound (w := (152707 / 1847293)) (n := 12)
    (lo := (165708717 / 1000000000)) (hi := (82854359 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 847293) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 847293) = 1/(847293 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-82854359 / 500000000) (-165708717 / 1000000000) (Real.log (847293 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (618609977 / 1000000000) ≤ -Real.log (500000000000 / 928172942817) ∧
    -Real.log (500000000000 / 928172942817) ≤ (309304989 / 500000000) := by
  have h := checkLog_sound (w := (428172942817 / 1428172942817)) (n := 12)
    (lo := (618609977 / 1000000000)) (hi := (309304989 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((928172942817 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(928172942817 / 500000000000) = 1/(500000000000 / 928172942817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (618609977 / 1000000000) (309304989 / 500000000) (Real.log (928172942817 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (928172942817 / 500000000000) = -Real.log (500000000000 / 928172942817) := by
    rw [show ((928172942817 / 500000000000) : ℝ) = ((500000000000 / 928172942817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (123979567 / 200000000) ≤ -Real.log (500000000000 / 929369067561) ∧
    -Real.log (500000000000 / 929369067561) ≤ (154974459 / 250000000) := by
  have h := checkLog_sound (w := (429369067561 / 1429369067561)) (n := 12)
    (lo := (123979567 / 200000000)) (hi := (154974459 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((929369067561 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(929369067561 / 500000000000) = 1/(500000000000 / 929369067561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (123979567 / 200000000) (154974459 / 250000000) (Real.log (929369067561 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (929369067561 / 500000000000) = -Real.log (500000000000 / 929369067561) := by
    rw [show ((929369067561 / 500000000000) : ℝ) = ((500000000000 / 929369067561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (54030297 / 125000000) ≤ -Real.log (250000000000 / 385177125493) ∧
    -Real.log (250000000000 / 385177125493) ≤ (432242377 / 1000000000) := by
  have h := checkLog_sound (w := (135177125493 / 635177125493)) (n := 12)
    (lo := (54030297 / 125000000)) (hi := (432242377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((385177125493 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(385177125493 / 250000000000) = 1/(250000000000 / 385177125493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (54030297 / 125000000) (432242377 / 1000000000) (Real.log (385177125493 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (385177125493 / 250000000000) = -Real.log (250000000000 / 385177125493) := by
    rw [show ((385177125493 / 250000000000) : ℝ) = ((250000000000 / 385177125493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (108281101 / 250000000) ≤ -Real.log (50000000000 / 77103402431) ∧
    -Real.log (50000000000 / 77103402431) ≤ (86624881 / 200000000) := by
  have h := checkLog_sound (w := (27103402431 / 127103402431)) (n := 12)
    (lo := (108281101 / 250000000)) (hi := (86624881 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((77103402431 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(77103402431 / 50000000000) = 1/(50000000000 / 77103402431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (108281101 / 250000000) (86624881 / 200000000) (Real.log (77103402431 / 50000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (77103402431 / 50000000000) = -Real.log (50000000000 / 77103402431) := by
    rw [show ((77103402431 / 50000000000) : ℝ) = ((50000000000 / 77103402431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (307189081 / 1000000000) ≤ -Real.log (3125000000 / 4248743809) ∧
    -Real.log (3125000000 / 4248743809) ≤ (153594541 / 500000000) := by
  have h := checkLog_sound (w := (1123743809 / 7373743809)) (n := 12)
    (lo := (307189081 / 1000000000)) (hi := (153594541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4248743809 / 3125000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4248743809 / 3125000000) = 1/(3125000000 / 4248743809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (307189081 / 1000000000) (153594541 / 500000000) (Real.log (4248743809 / 3125000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4248743809 / 3125000000) = -Real.log (3125000000 / 4248743809) := by
    rw [show ((4248743809 / 3125000000) : ℝ) = ((3125000000 / 4248743809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (153910903 / 500000000) ≤ -Real.log (500000000000 / 680229271339) ∧
    -Real.log (500000000000 / 680229271339) ≤ (307821807 / 1000000000) := by
  have h := checkLog_sound (w := (180229271339 / 1180229271339)) (n := 12)
    (lo := (153910903 / 500000000)) (hi := (307821807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((680229271339 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(680229271339 / 500000000000) = 1/(500000000000 / 680229271339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (153910903 / 500000000) (307821807 / 1000000000) (Real.log (680229271339 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (680229271339 / 500000000000) = -Real.log (500000000000 / 680229271339) := by
    rw [show ((680229271339 / 500000000000) : ℝ) = ((500000000000 / 680229271339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (5898907 / 250000000) ≤ -Real.log (976680572151 / 1000000000000) ∧
    -Real.log (976680572151 / 1000000000000) ≤ (23595629 / 1000000000) := by
  have h := checkLog_sound (w := (23319427849 / 1976680572151)) (n := 12)
    (lo := (5898907 / 250000000)) (hi := (23595629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 976680572151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 976680572151) = 1/(976680572151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-23595629 / 1000000000) (-5898907 / 250000000) (Real.log (976680572151 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (734347 / 31250000) ≤ -Real.log (244193712399 / 250000000000) ∧
    -Real.log (244193712399 / 250000000000) ≤ (4699821 / 200000000) := by
  have h := checkLog_sound (w := (5806287601 / 494193712399)) (n := 12)
    (lo := (734347 / 31250000)) (hi := (4699821 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244193712399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244193712399) = 1/(244193712399 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-4699821 / 200000000) (-734347 / 31250000) (Real.log (244193712399 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell085

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell086Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell086
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (16444699 / 62500000) ≤ -Real.log (5120 / 6661) ∧
    -Real.log (5120 / 6661) ≤ (52623037 / 200000000) := by
  have h := checkLog_sound (w := (1541 / 11781)) (n := 12)
    (lo := (16444699 / 62500000)) (hi := (52623037 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6661 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6661 / 5120) = 1/(5120 / 6661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (16444699 / 62500000) (52623037 / 200000000) (Real.log (6661 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6661 / 5120) = -Real.log (5120 / 6661) := by
    rw [show ((6661 / 5120) : ℝ) = ((5120 / 6661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (358071007 / 1000000000) ≤ -Real.log (3579 / 5120) ∧
    -Real.log (3579 / 5120) ≤ (11189719 / 31250000) := by
  have h := checkLog_sound (w := (1541 / 8699)) (n := 12)
    (lo := (358071007 / 1000000000)) (hi := (11189719 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3579) = 1/(3579 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-11189719 / 31250000) (-358071007 / 1000000000) (Real.log (3579 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (2626647 / 10000000) ≤ -Real.log (2560 / 3329) ∧
    -Real.log (2560 / 3329) ≤ (262664701 / 1000000000) := by
  have h := checkLog_sound (w := (769 / 5889)) (n := 12)
    (lo := (2626647 / 10000000)) (hi := (262664701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3329 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3329 / 2560) = 1/(2560 / 3329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (2626647 / 10000000) (262664701 / 1000000000) (Real.log (3329 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3329 / 2560) = -Real.log (2560 / 3329) := by
    rw [show ((3329 / 2560) : ℝ) = ((2560 / 3329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (71446627 / 200000000) ≤ -Real.log (1791 / 2560) ∧
    -Real.log (1791 / 2560) ≤ (22327071 / 62500000) := by
  have h := checkLog_sound (w := (769 / 4351)) (n := 12)
    (lo := (71446627 / 200000000)) (hi := (22327071 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1791) = 1/(1791 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-22327071 / 62500000) (-71446627 / 200000000) (Real.log (1791 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (96646409 / 500000000) ≤ -Real.log (500000 / 606619) ∧
    -Real.log (500000 / 606619) ≤ (193292819 / 1000000000) := by
  have h := checkLog_sound (w := (106619 / 1106619)) (n := 12)
    (lo := (96646409 / 500000000)) (hi := (193292819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((606619 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(606619 / 500000) = 1/(500000 / 606619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (96646409 / 500000000) (193292819 / 1000000000) (Real.log (606619 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (606619 / 500000) = -Real.log (500000 / 606619) := by
    rw [show ((606619 / 500000) : ℝ) = ((500000 / 606619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (23982949 / 100000000) ≤ -Real.log (393381 / 500000) ∧
    -Real.log (393381 / 500000) ≤ (239829491 / 1000000000) := by
  have h := checkLog_sound (w := (106619 / 893381)) (n := 12)
    (lo := (23982949 / 100000000)) (hi := (239829491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 393381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 393381) = 1/(393381 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-239829491 / 1000000000) (-23982949 / 100000000) (Real.log (393381 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (193638939 / 1000000000) ≤ -Real.log (500000 / 606829) ∧
    -Real.log (500000 / 606829) ≤ (9681947 / 50000000) := by
  have h := checkLog_sound (w := (106829 / 1106829)) (n := 12)
    (lo := (193638939 / 1000000000)) (hi := (9681947 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((606829 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(606829 / 500000) = 1/(500000 / 606829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (193638939 / 1000000000) (9681947 / 50000000) (Real.log (606829 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (606829 / 500000) = -Real.log (500000 / 606829) := by
    rw [show ((606829 / 500000) : ℝ) = ((500000 / 606829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (120181733 / 500000000) ≤ -Real.log (393171 / 500000) ∧
    -Real.log (393171 / 500000) ≤ (240363467 / 1000000000) := by
  have h := checkLog_sound (w := (106829 / 893171)) (n := 12)
    (lo := (120181733 / 500000000)) (hi := (240363467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 393171) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 393171) = 1/(393171 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-240363467 / 1000000000) (-120181733 / 500000000) (Real.log (393171 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (142112221 / 1000000000) ≤ -Real.log (500000 / 576353) ∧
    -Real.log (500000 / 576353) ≤ (71056111 / 500000000) := by
  have h := checkLog_sound (w := (76353 / 1076353)) (n := 12)
    (lo := (142112221 / 1000000000)) (hi := (71056111 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((576353 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(576353 / 500000) = 1/(500000 / 576353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (142112221 / 1000000000) (71056111 / 500000000) (Real.log (576353 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (576353 / 500000) = -Real.log (500000 / 576353) := by
    rw [show ((576353 / 500000) : ℝ) = ((500000 / 576353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (165707537 / 1000000000) ≤ -Real.log (423647 / 500000) ∧
    -Real.log (423647 / 500000) ≤ (82853769 / 500000000) := by
  have h := checkLog_sound (w := (76353 / 923647)) (n := 12)
    (lo := (165707537 / 1000000000)) (hi := (82853769 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 423647) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 423647) = 1/(423647 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-82853769 / 500000000) (-165707537 / 1000000000) (Real.log (423647 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (569521 / 4000000) ≤ -Real.log (200000 / 230603) ∧
    -Real.log (200000 / 230603) ≤ (142380251 / 1000000000) := by
  have h := checkLog_sound (w := (30603 / 430603)) (n := 12)
    (lo := (569521 / 4000000)) (hi := (142380251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((230603 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(230603 / 200000) = 1/(200000 / 230603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (569521 / 4000000) (142380251 / 1000000000) (Real.log (230603 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (230603 / 200000) = -Real.log (200000 / 230603) := by
    rw [show ((230603 / 200000) : ℝ) = ((200000 / 230603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (83036147 / 500000000) ≤ -Real.log (169397 / 200000) ∧
    -Real.log (169397 / 200000) ≤ (33214459 / 200000000) := by
  have h := checkLog_sound (w := (30603 / 369397)) (n := 12)
    (lo := (83036147 / 500000000)) (hi := (33214459 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 169397) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 169397) = 1/(169397 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-33214459 / 200000000) (-83036147 / 500000000) (Real.log (169397 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (123979567 / 200000000) ≤ -Real.log (12500000000 / 23234226689) ∧
    -Real.log (12500000000 / 23234226689) ≤ (154974459 / 250000000) := by
  have h := checkLog_sound (w := (10734226689 / 35734226689)) (n := 12)
    (lo := (123979567 / 200000000)) (hi := (154974459 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23234226689 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23234226689 / 12500000000) = 1/(12500000000 / 23234226689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (123979567 / 200000000) (154974459 / 250000000) (Real.log (23234226689 / 12500000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (23234226689 / 12500000000) = -Real.log (12500000000 / 23234226689) := by
    rw [show ((23234226689 / 12500000000) : ℝ) = ((12500000000 / 23234226689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (621186191 / 1000000000) ≤ -Real.log (250000000000 / 465283598771) ∧
    -Real.log (250000000000 / 465283598771) ≤ (38824137 / 62500000) := by
  have h := checkLog_sound (w := (215283598771 / 715283598771)) (n := 12)
    (lo := (621186191 / 1000000000)) (hi := (38824137 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((465283598771 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(465283598771 / 250000000000) = 1/(250000000000 / 465283598771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (621186191 / 1000000000) (38824137 / 62500000) (Real.log (465283598771 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (465283598771 / 250000000000) = -Real.log (250000000000 / 465283598771) := by
    rw [show ((465283598771 / 250000000000) : ℝ) = ((250000000000 / 465283598771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (108280577 / 250000000) ≤ -Real.log (31250000000 / 48189525549) ∧
    -Real.log (31250000000 / 48189525549) ≤ (433122309 / 1000000000) := by
  have h := checkLog_sound (w := (16939525549 / 79439525549)) (n := 12)
    (lo := (108280577 / 250000000)) (hi := (433122309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48189525549 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48189525549 / 31250000000) = 1/(31250000000 / 48189525549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (108280577 / 250000000) (433122309 / 1000000000) (Real.log (48189525549 / 31250000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (48189525549 / 31250000000) = -Real.log (31250000000 / 48189525549) := by
    rw [show ((48189525549 / 31250000000) : ℝ) = ((31250000000 / 48189525549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (217001203 / 500000000) ≤ -Real.log (62500000000 / 96463911377) ∧
    -Real.log (62500000000 / 96463911377) ≤ (434002407 / 1000000000) := by
  have h := checkLog_sound (w := (33963911377 / 158963911377)) (n := 12)
    (lo := (217001203 / 500000000)) (hi := (434002407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((96463911377 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(96463911377 / 62500000000) = 1/(62500000000 / 96463911377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (217001203 / 500000000) (434002407 / 1000000000) (Real.log (96463911377 / 62500000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (96463911377 / 62500000000) = -Real.log (62500000000 / 96463911377) := by
    rw [show ((96463911377 / 62500000000) : ℝ) = ((62500000000 / 96463911377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (153909879 / 500000000) ≤ -Real.log (250000000000 / 340113939199) ∧
    -Real.log (250000000000 / 340113939199) ≤ (307819759 / 1000000000) := by
  have h := checkLog_sound (w := (90113939199 / 590113939199)) (n := 12)
    (lo := (153909879 / 500000000)) (hi := (307819759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((340113939199 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(340113939199 / 250000000000) = 1/(250000000000 / 340113939199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (153909879 / 500000000) (307819759 / 1000000000) (Real.log (340113939199 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (340113939199 / 250000000000) = -Real.log (250000000000 / 340113939199) := by
    rw [show ((340113939199 / 250000000000) : ℝ) = ((250000000000 / 340113939199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4819571 / 15625000) ≤ -Real.log (25000000000 / 34032922661) ∧
    -Real.log (25000000000 / 34032922661) ≤ (61690509 / 200000000) := by
  have h := checkLog_sound (w := (9032922661 / 59032922661)) (n := 12)
    (lo := (4819571 / 15625000)) (hi := (61690509 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34032922661 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(34032922661 / 25000000000) = 1/(25000000000 / 34032922661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4819571 / 15625000) (61690509 / 200000000) (Real.log (34032922661 / 25000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (34032922661 / 25000000000) = -Real.log (25000000000 / 34032922661) := by
    rw [show ((34032922661 / 25000000000) : ℝ) = ((25000000000 / 34032922661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (23692043 / 1000000000) ≤ -Real.log (39063456391 / 40000000000) ∧
    -Real.log (39063456391 / 40000000000) ≤ (5923011 / 250000000) := by
  have h := checkLog_sound (w := (936543609 / 79063456391)) (n := 12)
    (lo := (23692043 / 1000000000)) (hi := (5923011 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39063456391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39063456391) = 1/(39063456391 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-5923011 / 250000000) (-23692043 / 1000000000) (Real.log (39063456391 / 40000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (4719063 / 200000000) ≤ -Real.log (244170219391 / 250000000000) ∧
    -Real.log (244170219391 / 250000000000) ≤ (5898829 / 250000000) := by
  have h := checkLog_sound (w := (5829780609 / 494170219391)) (n := 12)
    (lo := (4719063 / 200000000)) (hi := (5898829 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244170219391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244170219391) = 1/(244170219391 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-5898829 / 250000000) (-4719063 / 200000000) (Real.log (244170219391 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell086

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell087Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell087
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (52713093 / 200000000) ≤ -Real.log (640 / 833) ∧
    -Real.log (640 / 833) ≤ (131782733 / 500000000) := by
  have h := checkLog_sound (w := (193 / 1473)) (n := 12)
    (lo := (52713093 / 200000000)) (hi := (131782733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((833 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(833 / 640) = 1/(640 / 833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (52713093 / 200000000) (131782733 / 500000000) (Real.log (833 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (833 / 640) = -Real.log (640 / 833) := by
    rw [show ((833 / 640) : ℝ) = ((640 / 833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (358909581 / 1000000000) ≤ -Real.log (447 / 640) ∧
    -Real.log (447 / 640) ≤ (179454791 / 500000000) := by
  have h := checkLog_sound (w := (193 / 1087)) (n := 12)
    (lo := (358909581 / 1000000000)) (hi := (179454791 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 447) = 1/(447 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-179454791 / 500000000) (-358909581 / 1000000000) (Real.log (447 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (16444699 / 62500000) ≤ -Real.log (5120 / 6661) ∧
    -Real.log (5120 / 6661) ≤ (52623037 / 200000000) := by
  have h := checkLog_sound (w := (1541 / 11781)) (n := 12)
    (lo := (16444699 / 62500000)) (hi := (52623037 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6661 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6661 / 5120) = 1/(5120 / 6661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (16444699 / 62500000) (52623037 / 200000000) (Real.log (6661 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6661 / 5120) = -Real.log (5120 / 6661) := by
    rw [show ((6661 / 5120) : ℝ) = ((5120 / 6661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (358071007 / 1000000000) ≤ -Real.log (3579 / 5120) ∧
    -Real.log (3579 / 5120) ≤ (11189719 / 31250000) := by
  have h := checkLog_sound (w := (1541 / 8699)) (n := 12)
    (lo := (358071007 / 1000000000)) (hi := (11189719 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3579) = 1/(3579 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-11189719 / 31250000) (-358071007 / 1000000000) (Real.log (3579 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (38727623 / 200000000) ≤ -Real.log (1000000 / 1213657) ∧
    -Real.log (1000000 / 1213657) ≤ (48409529 / 250000000) := by
  have h := checkLog_sound (w := (213657 / 2213657)) (n := 12)
    (lo := (38727623 / 200000000)) (hi := (48409529 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1213657 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1213657 / 1000000) = 1/(1000000 / 1213657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (38727623 / 200000000) (48409529 / 250000000) (Real.log (1213657 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1213657 / 1000000) = -Real.log (1000000 / 1213657) := by
    rw [show ((1213657 / 1000000) : ℝ) = ((1000000 / 1213657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (120181097 / 500000000) ≤ -Real.log (786343 / 1000000) ∧
    -Real.log (786343 / 1000000) ≤ (48072439 / 200000000) := by
  have h := checkLog_sound (w := (213657 / 1786343)) (n := 12)
    (lo := (120181097 / 500000000)) (hi := (48072439 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 786343) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 786343) = 1/(786343 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-48072439 / 200000000) (-120181097 / 500000000) (Real.log (786343 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (193984117 / 1000000000) ≤ -Real.log (1000000 / 1214077) ∧
    -Real.log (1000000 / 1214077) ≤ (96992059 / 500000000) := by
  have h := checkLog_sound (w := (214077 / 2214077)) (n := 12)
    (lo := (193984117 / 1000000000)) (hi := (96992059 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1214077 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1214077 / 1000000) = 1/(1000000 / 1214077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (193984117 / 1000000000) (96992059 / 500000000) (Real.log (1214077 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1214077 / 1000000) = -Real.log (1000000 / 1214077) := by
    rw [show ((1214077 / 1000000) : ℝ) = ((1000000 / 1214077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (48179291 / 200000000) ≤ -Real.log (785923 / 1000000) ∧
    -Real.log (785923 / 1000000) ≤ (30112057 / 125000000) := by
  have h := checkLog_sound (w := (214077 / 1785923)) (n := 12)
    (lo := (48179291 / 200000000)) (hi := (30112057 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 785923) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 785923) = 1/(785923 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-30112057 / 125000000) (-48179291 / 200000000) (Real.log (785923 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (142379383 / 1000000000) ≤ -Real.log (500000 / 576507) ∧
    -Real.log (500000 / 576507) ≤ (17797423 / 125000000) := by
  have h := checkLog_sound (w := (76507 / 1076507)) (n := 12)
    (lo := (142379383 / 1000000000)) (hi := (17797423 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((576507 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(576507 / 500000) = 1/(500000 / 576507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (142379383 / 1000000000) (17797423 / 125000000) (Real.log (576507 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (576507 / 500000) = -Real.log (500000 / 576507) := by
    rw [show ((576507 / 500000) : ℝ) = ((500000 / 576507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (166071113 / 1000000000) ≤ -Real.log (423493 / 500000) ∧
    -Real.log (423493 / 500000) ≤ (83035557 / 500000000) := by
  have h := checkLog_sound (w := (76507 / 923493)) (n := 12)
    (lo := (166071113 / 1000000000)) (hi := (83035557 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 423493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 423493) = 1/(423493 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-83035557 / 500000000) (-166071113 / 1000000000) (Real.log (423493 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (7132367 / 50000000) ≤ -Real.log (1000000 / 1153323) ∧
    -Real.log (1000000 / 1153323) ≤ (142647341 / 1000000000) := by
  have h := checkLog_sound (w := (153323 / 2153323)) (n := 12)
    (lo := (7132367 / 50000000)) (hi := (142647341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1153323 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1153323 / 1000000) = 1/(1000000 / 1153323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (7132367 / 50000000) (142647341 / 1000000000) (Real.log (1153323 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1153323 / 1000000) = -Real.log (1000000 / 1153323) := by
    rw [show ((1153323 / 1000000) : ℝ) = ((1000000 / 1153323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (83218001 / 500000000) ≤ -Real.log (846677 / 1000000) ∧
    -Real.log (846677 / 1000000) ≤ (166436003 / 1000000000) := by
  have h := checkLog_sound (w := (153323 / 1846677)) (n := 12)
    (lo := (83218001 / 500000000)) (hi := (166436003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 846677) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 846677) = 1/(846677 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-166436003 / 1000000000) (-83218001 / 500000000) (Real.log (846677 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (621186191 / 1000000000) ≤ -Real.log (500000000000 / 930567197541) ∧
    -Real.log (500000000000 / 930567197541) ≤ (38824137 / 62500000) := by
  have h := checkLog_sound (w := (430567197541 / 1430567197541)) (n := 12)
    (lo := (621186191 / 1000000000)) (hi := (38824137 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((930567197541 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(930567197541 / 500000000000) = 1/(500000000000 / 930567197541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (621186191 / 1000000000) (38824137 / 62500000) (Real.log (930567197541 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (930567197541 / 500000000000) = -Real.log (500000000000 / 930567197541) := by
    rw [show ((930567197541 / 500000000000) : ℝ) = ((500000000000 / 930567197541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (622475047 / 1000000000) ≤ -Real.log (31250000000 / 58235458613) ∧
    -Real.log (31250000000 / 58235458613) ≤ (77809381 / 125000000) := by
  have h := checkLog_sound (w := (26985458613 / 89485458613)) (n := 12)
    (lo := (622475047 / 1000000000)) (hi := (77809381 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((58235458613 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(58235458613 / 31250000000) = 1/(31250000000 / 58235458613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (622475047 / 1000000000) (77809381 / 125000000) (Real.log (58235458613 / 31250000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (58235458613 / 31250000000) = -Real.log (31250000000 / 58235458613) := by
    rw [show ((58235458613 / 31250000000) : ℝ) = ((31250000000 / 58235458613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (43400031 / 100000000) ≤ -Real.log (62500000000 / 96463709221) ∧
    -Real.log (62500000000 / 96463709221) ≤ (434000311 / 1000000000) := by
  have h := checkLog_sound (w := (33963709221 / 158963709221)) (n := 12)
    (lo := (43400031 / 100000000)) (hi := (434000311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((96463709221 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(96463709221 / 62500000000) = 1/(62500000000 / 96463709221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (43400031 / 100000000) (434000311 / 1000000000) (Real.log (96463709221 / 62500000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (96463709221 / 62500000000) = -Real.log (62500000000 / 96463709221) := by
    rw [show ((96463709221 / 62500000000) : ℝ) = ((62500000000 / 96463709221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (434880573 / 1000000000) ≤ -Real.log (250000000000 / 386194639933) ∧
    -Real.log (250000000000 / 386194639933) ≤ (217440287 / 500000000) := by
  have h := checkLog_sound (w := (136194639933 / 636194639933)) (n := 12)
    (lo := (434880573 / 1000000000)) (hi := (217440287 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((386194639933 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(386194639933 / 250000000000) = 1/(250000000000 / 386194639933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (434880573 / 1000000000) (217440287 / 500000000) (Real.log (386194639933 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (386194639933 / 250000000000) = -Real.log (250000000000 / 386194639933) := by
    rw [show ((386194639933 / 250000000000) : ℝ) = ((250000000000 / 386194639933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (4819539 / 15625000) ≤ -Real.log (250000000000 / 340328529633) ∧
    -Real.log (250000000000 / 340328529633) ≤ (308450497 / 1000000000) := by
  have h := checkLog_sound (w := (90328529633 / 590328529633)) (n := 12)
    (lo := (4819539 / 15625000)) (hi := (308450497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((340328529633 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(340328529633 / 250000000000) = 1/(250000000000 / 340328529633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4819539 / 15625000) (308450497 / 1000000000) (Real.log (340328529633 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (340328529633 / 250000000000) = -Real.log (250000000000 / 340328529633) := by
    rw [show ((340328529633 / 250000000000) : ℝ) = ((250000000000 / 340328529633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (309083343 / 1000000000) ≤ -Real.log (62500000000 / 85135993419) ∧
    -Real.log (62500000000 / 85135993419) ≤ (19317709 / 62500000) := by
  have h := checkLog_sound (w := (22635993419 / 147635993419)) (n := 12)
    (lo := (309083343 / 1000000000)) (hi := (19317709 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((85135993419 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(85135993419 / 62500000000) = 1/(62500000000 / 85135993419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (309083343 / 1000000000) (19317709 / 62500000) (Real.log (85135993419 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (85135993419 / 62500000000) = -Real.log (62500000000 / 85135993419) := by
    rw [show ((85135993419 / 62500000000) : ℝ) = ((62500000000 / 85135993419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (11894331 / 500000000) ≤ -Real.log (976492057671 / 1000000000000) ∧
    -Real.log (976492057671 / 1000000000000) ≤ (23788663 / 1000000000) := by
  have h := checkLog_sound (w := (23507942329 / 1976492057671)) (n := 12)
    (lo := (11894331 / 500000000)) (hi := (23788663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 976492057671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 976492057671) = 1/(976492057671 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-23788663 / 1000000000) (-11894331 / 500000000) (Real.log (976492057671 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (23691729 / 1000000000) ≤ -Real.log (244146678951 / 250000000000) ∧
    -Real.log (244146678951 / 250000000000) ≤ (2369173 / 100000000) := by
  have h := checkLog_sound (w := (5853321049 / 494146678951)) (n := 12)
    (lo := (23691729 / 1000000000)) (hi := (2369173 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244146678951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244146678951) = 1/(244146678951 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-2369173 / 100000000) (-23691729 / 1000000000) (Real.log (244146678951 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell087

end


