-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell109Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell109Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T16:51:04.228459+00:00
-- url     : https://prove2.me/theorems/852d6ecc-9883-41bf-859f-019a422d45de
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell109Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell110…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell109Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell110Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell111Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell112Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell113Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell114Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell115Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell109Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell110Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell111Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell112Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell113Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell114Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell115Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell109Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell110Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell111Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell112Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell113Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell114Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell115Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell109Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell110Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell111Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell112Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell113Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell114Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell115Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell109Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell109
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

theorem reflection_log_1_neg : (8544397 / 31250000) ≤ -Real.log (512 / 673) ∧
    -Real.log (512 / 673) ≤ (54684141 / 200000000) := by
  have h := checkLog_sound (w := (161 / 1185)) (n := 12)
    (lo := (8544397 / 31250000)) (hi := (54684141 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((673 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(673 / 512) = 1/(512 / 673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (8544397 / 31250000) (54684141 / 200000000) (Real.log (673 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (673 / 512) = -Real.log (512 / 673) := by
    rw [show ((673 / 512) : ℝ) = ((512 / 673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (377538401 / 1000000000) ≤ -Real.log (351 / 512) ∧
    -Real.log (351 / 512) ≤ (188769201 / 500000000) := by
  have h := checkLog_sound (w := (161 / 863)) (n := 12)
    (lo := (377538401 / 1000000000)) (hi := (188769201 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 351) = 1/(351 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-188769201 / 500000000) (-377538401 / 1000000000) (Real.log (351 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (272974839 / 1000000000) ≤ -Real.log (5120 / 6727) ∧
    -Real.log (5120 / 6727) ≤ (6824371 / 25000000) := by
  have h := checkLog_sound (w := (1607 / 11847)) (n := 12)
    (lo := (272974839 / 1000000000)) (hi := (6824371 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6727 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6727 / 5120) = 1/(5120 / 6727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (272974839 / 1000000000) (6824371 / 25000000) (Real.log (6727 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6727 / 5120) = -Real.log (5120 / 6727) := by
    rw [show ((6727 / 5120) : ℝ) = ((5120 / 6727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (75336813 / 200000000) ≤ -Real.log (3513 / 5120) ∧
    -Real.log (3513 / 5120) ≤ (188342033 / 500000000) := by
  have h := checkLog_sound (w := (1607 / 8633)) (n := 12)
    (lo := (75336813 / 200000000)) (hi := (188342033 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3513) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3513) = 1/(3513 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-188342033 / 500000000) (-75336813 / 200000000) (Real.log (3513 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (25151807 / 125000000) ≤ -Real.log (1000000 / 1222887) ∧
    -Real.log (1000000 / 1222887) ≤ (201214457 / 1000000000) := by
  have h := checkLog_sound (w := (222887 / 2222887)) (n := 12)
    (lo := (25151807 / 125000000)) (hi := (201214457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1222887 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1222887 / 1000000) = 1/(1000000 / 1222887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (25151807 / 125000000) (201214457 / 1000000000) (Real.log (1222887 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1222887 / 1000000) = -Real.log (1000000 / 1222887) := by
    rw [show ((1222887 / 1000000) : ℝ) = ((1000000 / 1222887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (63042377 / 250000000) ≤ -Real.log (777113 / 1000000) ∧
    -Real.log (777113 / 1000000) ≤ (252169509 / 1000000000) := by
  have h := checkLog_sound (w := (222887 / 1777113)) (n := 12)
    (lo := (63042377 / 250000000)) (hi := (252169509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 777113) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 777113) = 1/(777113 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-252169509 / 1000000000) (-63042377 / 250000000) (Real.log (777113 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (25194833 / 125000000) ≤ -Real.log (250000 / 305827) ∧
    -Real.log (250000 / 305827) ≤ (40311733 / 200000000) := by
  have h := checkLog_sound (w := (55827 / 555827)) (n := 12)
    (lo := (25194833 / 125000000)) (hi := (40311733 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305827 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305827 / 250000) = 1/(250000 / 305827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (25194833 / 125000000) (40311733 / 200000000) (Real.log (305827 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (305827 / 250000) = -Real.log (250000 / 305827) := by
    rw [show ((305827 / 250000) : ℝ) = ((250000 / 305827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (252711403 / 1000000000) ≤ -Real.log (194173 / 250000) ∧
    -Real.log (194173 / 250000) ≤ (63177851 / 250000000) := by
  have h := checkLog_sound (w := (55827 / 444173)) (n := 12)
    (lo := (252711403 / 1000000000)) (hi := (63177851 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 194173) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 194173) = 1/(194173 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-63177851 / 250000000) (-252711403 / 1000000000) (Real.log (194173 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (148251887 / 1000000000) ≤ -Real.log (200000 / 231961) ∧
    -Real.log (200000 / 231961) ≤ (9265743 / 62500000) := by
  have h := checkLog_sound (w := (31961 / 431961)) (n := 12)
    (lo := (148251887 / 1000000000)) (hi := (9265743 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((231961 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(231961 / 200000) = 1/(200000 / 231961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (148251887 / 1000000000) (9265743 / 62500000) (Real.log (231961 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (231961 / 200000) = -Real.log (200000 / 231961) := by
    rw [show ((231961 / 200000) : ℝ) = ((200000 / 231961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (174121271 / 1000000000) ≤ -Real.log (168039 / 200000) ∧
    -Real.log (168039 / 200000) ≤ (21765159 / 125000000) := by
  have h := checkLog_sound (w := (31961 / 368039)) (n := 12)
    (lo := (174121271 / 1000000000)) (hi := (21765159 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 168039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 168039) = 1/(168039 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-21765159 / 125000000) (-174121271 / 1000000000) (Real.log (168039 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (74259569 / 500000000) ≤ -Real.log (200000 / 232023) ∧
    -Real.log (200000 / 232023) ≤ (148519139 / 1000000000) := by
  have h := checkLog_sound (w := (32023 / 432023)) (n := 12)
    (lo := (74259569 / 500000000)) (hi := (148519139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((232023 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(232023 / 200000) = 1/(200000 / 232023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (74259569 / 500000000) (148519139 / 1000000000) (Real.log (232023 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (232023 / 200000) = -Real.log (200000 / 232023) := by
    rw [show ((232023 / 200000) : ℝ) = ((200000 / 232023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (174490301 / 1000000000) ≤ -Real.log (167977 / 200000) ∧
    -Real.log (167977 / 200000) ≤ (87245151 / 500000000) := by
  have h := checkLog_sound (w := (32023 / 367977)) (n := 12)
    (lo := (174490301 / 1000000000)) (hi := (87245151 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 167977) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 167977) = 1/(167977 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-87245151 / 500000000) (-174490301 / 1000000000) (Real.log (167977 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (129931781 / 200000000) ≤ -Real.log (125000000000 / 239360945061) ∧
    -Real.log (125000000000 / 239360945061) ≤ (324829453 / 500000000) := by
  have h := checkLog_sound (w := (114360945061 / 364360945061)) (n := 12)
    (lo := (129931781 / 200000000)) (hi := (324829453 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((239360945061 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(239360945061 / 125000000000) = 1/(125000000000 / 239360945061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (129931781 / 200000000) (324829453 / 500000000) (Real.log (239360945061 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (239360945061 / 125000000000) = -Real.log (125000000000 / 239360945061) := by
    rw [show ((239360945061 / 125000000000) : ℝ) = ((125000000000 / 239360945061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (325479553 / 500000000) ≤ -Real.log (50000000000 / 95868945869) ∧
    -Real.log (50000000000 / 95868945869) ≤ (650959107 / 1000000000) := by
  have h := checkLog_sound (w := (45868945869 / 145868945869)) (n := 12)
    (lo := (325479553 / 500000000)) (hi := (650959107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((95868945869 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(95868945869 / 50000000000) = 1/(50000000000 / 95868945869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (325479553 / 500000000) (650959107 / 1000000000) (Real.log (95868945869 / 50000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (95868945869 / 50000000000) = -Real.log (50000000000 / 95868945869) := by
    rw [show ((95868945869 / 50000000000) : ℝ) = ((50000000000 / 95868945869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (113345991 / 250000000) ≤ -Real.log (250000000000 / 393407072073) ∧
    -Real.log (250000000000 / 393407072073) ≤ (90676793 / 200000000) := by
  have h := checkLog_sound (w := (143407072073 / 643407072073)) (n := 12)
    (lo := (113345991 / 250000000)) (hi := (90676793 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((393407072073 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(393407072073 / 250000000000) = 1/(250000000000 / 393407072073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (113345991 / 250000000) (90676793 / 200000000) (Real.log (393407072073 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (393407072073 / 250000000000) = -Real.log (250000000000 / 393407072073) := by
    rw [show ((393407072073 / 250000000000) : ℝ) = ((250000000000 / 393407072073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (113567517 / 250000000) ≤ -Real.log (500000000000 / 787511651981) ∧
    -Real.log (500000000000 / 787511651981) ≤ (454270069 / 1000000000) := by
  have h := checkLog_sound (w := (287511651981 / 1287511651981)) (n := 12)
    (lo := (113567517 / 250000000)) (hi := (454270069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((787511651981 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(787511651981 / 500000000000) = 1/(500000000000 / 787511651981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (113567517 / 250000000) (454270069 / 1000000000) (Real.log (787511651981 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (787511651981 / 500000000000) = -Real.log (500000000000 / 787511651981) := by
    rw [show ((787511651981 / 500000000000) : ℝ) = ((500000000000 / 787511651981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (161186579 / 500000000) ≤ -Real.log (62500000000 / 86274986759) ∧
    -Real.log (62500000000 / 86274986759) ≤ (322373159 / 1000000000) := by
  have h := checkLog_sound (w := (23774986759 / 148774986759)) (n := 12)
    (lo := (161186579 / 500000000)) (hi := (322373159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((86274986759 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(86274986759 / 62500000000) = 1/(62500000000 / 86274986759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (161186579 / 500000000) (322373159 / 1000000000) (Real.log (86274986759 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (86274986759 / 62500000000) = -Real.log (62500000000 / 86274986759) := by
    rw [show ((86274986759 / 62500000000) : ℝ) = ((62500000000 / 86274986759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (323009439 / 1000000000) ≤ -Real.log (125000000000 / 172659798663) ∧
    -Real.log (125000000000 / 172659798663) ≤ (2018809 / 6250000) := by
  have h := checkLog_sound (w := (47659798663 / 297659798663)) (n := 12)
    (lo := (323009439 / 1000000000)) (hi := (2018809 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((172659798663 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(172659798663 / 125000000000) = 1/(125000000000 / 172659798663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (323009439 / 1000000000) (2018809 / 6250000) (Real.log (172659798663 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (172659798663 / 125000000000) = -Real.log (125000000000 / 172659798663) := by
    rw [show ((172659798663 / 125000000000) : ℝ) = ((125000000000 / 172659798663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (25971163 / 1000000000) ≤ -Real.log (38974527471 / 40000000000) ∧
    -Real.log (38974527471 / 40000000000) ≤ (6492791 / 250000000) := by
  have h := checkLog_sound (w := (1025472529 / 78974527471)) (n := 12)
    (lo := (25971163 / 1000000000)) (hi := (6492791 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38974527471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38974527471) = 1/(38974527471 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-6492791 / 250000000) (-25971163 / 1000000000) (Real.log (38974527471 / 40000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (25869383 / 1000000000) ≤ -Real.log (38978494479 / 40000000000) ∧
    -Real.log (38978494479 / 40000000000) ≤ (3233673 / 125000000) := by
  have h := checkLog_sound (w := (1021505521 / 78978494479)) (n := 12)
    (lo := (25869383 / 1000000000)) (hi := (3233673 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38978494479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38978494479) = 1/(38978494479 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-3233673 / 125000000) (-25869383 / 1000000000) (Real.log (38978494479 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell109

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell110Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell110
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

theorem reflection_log_1_neg : (27386637 / 100000000) ≤ -Real.log (5120 / 6733) ∧
    -Real.log (5120 / 6733) ≤ (273866371 / 1000000000) := by
  have h := checkLog_sound (w := (1613 / 11853)) (n := 12)
    (lo := (27386637 / 100000000)) (hi := (273866371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6733 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6733 / 5120) = 1/(5120 / 6733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (27386637 / 100000000) (273866371 / 1000000000) (Real.log (6733 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6733 / 5120) = -Real.log (5120 / 6733) := by
    rw [show ((6733 / 5120) : ℝ) = ((5120 / 6733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (378393467 / 1000000000) ≤ -Real.log (3507 / 5120) ∧
    -Real.log (3507 / 5120) ≤ (94598367 / 250000000) := by
  have h := checkLog_sound (w := (1613 / 8627)) (n := 12)
    (lo := (378393467 / 1000000000)) (hi := (94598367 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3507) = 1/(3507 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-94598367 / 250000000) (-378393467 / 1000000000) (Real.log (3507 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (8544397 / 31250000) ≤ -Real.log (512 / 673) ∧
    -Real.log (512 / 673) ≤ (54684141 / 200000000) := by
  have h := checkLog_sound (w := (161 / 1185)) (n := 12)
    (lo := (8544397 / 31250000)) (hi := (54684141 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((673 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(673 / 512) = 1/(512 / 673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (8544397 / 31250000) (54684141 / 200000000) (Real.log (673 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (673 / 512) = -Real.log (512 / 673) := by
    rw [show ((673 / 512) : ℝ) = ((512 / 673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (377538401 / 1000000000) ≤ -Real.log (351 / 512) ∧
    -Real.log (351 / 512) ≤ (188769201 / 500000000) := by
  have h := checkLog_sound (w := (161 / 863)) (n := 12)
    (lo := (377538401 / 1000000000)) (hi := (188769201 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 351) = 1/(351 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-188769201 / 500000000) (-377538401 / 1000000000) (Real.log (351 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (201557847 / 1000000000) ≤ -Real.log (1000000 / 1223307) ∧
    -Real.log (1000000 / 1223307) ≤ (25194731 / 125000000) := by
  have h := checkLog_sound (w := (223307 / 2223307)) (n := 12)
    (lo := (201557847 / 1000000000)) (hi := (25194731 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1223307 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1223307 / 1000000) = 1/(1000000 / 1223307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (201557847 / 1000000000) (25194731 / 125000000) (Real.log (1223307 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1223307 / 1000000) = -Real.log (1000000 / 1223307) := by
    rw [show ((1223307 / 1000000) : ℝ) = ((1000000 / 1223307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (63177529 / 250000000) ≤ -Real.log (776693 / 1000000) ∧
    -Real.log (776693 / 1000000) ≤ (252710117 / 1000000000) := by
  have h := checkLog_sound (w := (223307 / 1776693)) (n := 12)
    (lo := (63177529 / 250000000)) (hi := (252710117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 776693) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 776693) = 1/(776693 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-252710117 / 1000000000) (-63177529 / 250000000) (Real.log (776693 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (201901937 / 1000000000) ≤ -Real.log (62500 / 76483) ∧
    -Real.log (62500 / 76483) ≤ (100950969 / 500000000) := by
  have h := checkLog_sound (w := (13983 / 138983)) (n := 12)
    (lo := (201901937 / 1000000000)) (hi := (100950969 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76483 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76483 / 62500) = 1/(62500 / 76483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (201901937 / 1000000000) (100950969 / 500000000) (Real.log (76483 / 62500)) := by
  have h := reflection_log_7_neg
  have he : Real.log (76483 / 62500) = -Real.log (62500 / 76483) := by
    rw [show ((76483 / 62500) : ℝ) = ((62500 / 76483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (15828269 / 62500000) ≤ -Real.log (48517 / 62500) ∧
    -Real.log (48517 / 62500) ≤ (50650461 / 200000000) := by
  have h := checkLog_sound (w := (13983 / 111017)) (n := 12)
    (lo := (15828269 / 62500000)) (hi := (50650461 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 48517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 48517) = 1/(48517 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-50650461 / 200000000) (-15828269 / 62500000) (Real.log (48517 / 62500)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (37129569 / 250000000) ≤ -Real.log (500000 / 580057) ∧
    -Real.log (500000 / 580057) ≤ (148518277 / 1000000000) := by
  have h := checkLog_sound (w := (80057 / 1080057)) (n := 12)
    (lo := (37129569 / 250000000)) (hi := (148518277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((580057 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(580057 / 500000) = 1/(500000 / 580057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (37129569 / 250000000) (148518277 / 1000000000) (Real.log (580057 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (580057 / 500000) = -Real.log (500000 / 580057) := by
    rw [show ((580057 / 500000) : ℝ) = ((500000 / 580057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (17448911 / 100000000) ≤ -Real.log (419943 / 500000) ∧
    -Real.log (419943 / 500000) ≤ (174489111 / 1000000000) := by
  have h := checkLog_sound (w := (80057 / 919943)) (n := 12)
    (lo := (17448911 / 100000000)) (hi := (174489111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 419943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 419943) = 1/(419943 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-174489111 / 1000000000) (-17448911 / 100000000) (Real.log (419943 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (148786317 / 1000000000) ≤ -Real.log (40000 / 46417) ∧
    -Real.log (40000 / 46417) ≤ (74393159 / 500000000) := by
  have h := checkLog_sound (w := (6417 / 86417)) (n := 12)
    (lo := (148786317 / 1000000000)) (hi := (74393159 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46417 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(46417 / 40000) = 1/(40000 / 46417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (148786317 / 1000000000) (74393159 / 500000000) (Real.log (46417 / 40000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (46417 / 40000) = -Real.log (40000 / 46417) := by
    rw [show ((46417 / 40000) : ℝ) = ((40000 / 46417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (174859467 / 1000000000) ≤ -Real.log (33583 / 40000) ∧
    -Real.log (33583 / 40000) ≤ (43714867 / 250000000) := by
  have h := checkLog_sound (w := (6417 / 73583)) (n := 12)
    (lo := (174859467 / 1000000000)) (hi := (43714867 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 33583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 33583) = 1/(33583 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-43714867 / 250000000) (-174859467 / 1000000000) (Real.log (33583 / 40000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (325479553 / 500000000) ≤ -Real.log (500000000000 / 958689458689) ∧
    -Real.log (500000000000 / 958689458689) ≤ (650959107 / 1000000000) := by
  have h := checkLog_sound (w := (458689458689 / 1458689458689)) (n := 12)
    (lo := (325479553 / 500000000)) (hi := (650959107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((958689458689 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(958689458689 / 500000000000) = 1/(500000000000 / 958689458689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (325479553 / 500000000) (650959107 / 1000000000) (Real.log (958689458689 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (958689458689 / 500000000000) = -Real.log (500000000000 / 958689458689) := by
    rw [show ((958689458689 / 500000000000) : ℝ) = ((500000000000 / 958689458689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (326129919 / 500000000) ≤ -Real.log (500000000000 / 959937268321) ∧
    -Real.log (500000000000 / 959937268321) ≤ (652259839 / 1000000000) := by
  have h := checkLog_sound (w := (459937268321 / 1459937268321)) (n := 12)
    (lo := (326129919 / 500000000)) (hi := (652259839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((959937268321 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(959937268321 / 500000000000) = 1/(500000000000 / 959937268321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (326129919 / 500000000) (652259839 / 1000000000) (Real.log (959937268321 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (959937268321 / 500000000000) = -Real.log (500000000000 / 959937268321) := by
    rw [show ((959937268321 / 500000000000) : ℝ) = ((500000000000 / 959937268321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (454267963 / 1000000000) ≤ -Real.log (62500000000 / 98438749287) ∧
    -Real.log (62500000000 / 98438749287) ≤ (113566991 / 250000000) := by
  have h := checkLog_sound (w := (35938749287 / 160938749287)) (n := 12)
    (lo := (454267963 / 1000000000)) (hi := (113566991 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98438749287 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98438749287 / 62500000000) = 1/(62500000000 / 98438749287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (454267963 / 1000000000) (113566991 / 250000000) (Real.log (98438749287 / 62500000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (98438749287 / 62500000000) = -Real.log (62500000000 / 98438749287) := by
    rw [show ((98438749287 / 62500000000) : ℝ) = ((62500000000 / 98438749287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (455154241 / 1000000000) ≤ -Real.log (5000000000 / 7882082569) ∧
    -Real.log (5000000000 / 7882082569) ≤ (227577121 / 500000000) := by
  have h := checkLog_sound (w := (2882082569 / 12882082569)) (n := 12)
    (lo := (455154241 / 1000000000)) (hi := (227577121 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7882082569 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7882082569 / 5000000000) = 1/(5000000000 / 7882082569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (455154241 / 1000000000) (227577121 / 500000000) (Real.log (7882082569 / 5000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (7882082569 / 5000000000) = -Real.log (5000000000 / 7882082569) := by
    rw [show ((7882082569 / 5000000000) : ℝ) = ((5000000000 / 7882082569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (161503693 / 500000000) ≤ -Real.log (500000000000 / 690637777031) ∧
    -Real.log (500000000000 / 690637777031) ≤ (323007387 / 1000000000) := by
  have h := checkLog_sound (w := (190637777031 / 1190637777031)) (n := 12)
    (lo := (161503693 / 500000000)) (hi := (323007387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((690637777031 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(690637777031 / 500000000000) = 1/(500000000000 / 690637777031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (161503693 / 500000000) (323007387 / 1000000000) (Real.log (690637777031 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (690637777031 / 500000000000) = -Real.log (500000000000 / 690637777031) := by
    rw [show ((690637777031 / 500000000000) : ℝ) = ((500000000000 / 690637777031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (40455723 / 125000000) ≤ -Real.log (500000000000 / 691078819641) ∧
    -Real.log (500000000000 / 691078819641) ≤ (64729157 / 200000000) := by
  have h := checkLog_sound (w := (191078819641 / 1191078819641)) (n := 12)
    (lo := (40455723 / 125000000)) (hi := (64729157 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((691078819641 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(691078819641 / 500000000000) = 1/(500000000000 / 691078819641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (40455723 / 125000000) (64729157 / 200000000) (Real.log (691078819641 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (691078819641 / 500000000000) = -Real.log (500000000000 / 691078819641) := by
    rw [show ((691078819641 / 500000000000) : ℝ) = ((500000000000 / 691078819641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (521463 / 20000000) ≤ -Real.log (1558822111 / 1600000000) ∧
    -Real.log (1558822111 / 1600000000) ≤ (26073151 / 1000000000) := by
  have h := checkLog_sound (w := (41177889 / 3158822111)) (n := 12)
    (lo := (521463 / 20000000)) (hi := (26073151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1558822111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1558822111) = 1/(1558822111 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-26073151 / 1000000000) (-521463 / 20000000) (Real.log (1558822111 / 1600000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (12985417 / 500000000) ≤ -Real.log (243590876751 / 250000000000) ∧
    -Real.log (243590876751 / 250000000000) ≤ (5194167 / 200000000) := by
  have h := checkLog_sound (w := (6409123249 / 493590876751)) (n := 12)
    (lo := (12985417 / 500000000)) (hi := (5194167 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243590876751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243590876751) = 1/(243590876751 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-5194167 / 200000000) (-12985417 / 500000000) (Real.log (243590876751 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell110

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell111Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell111
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

theorem reflection_log_1_neg : (274311837 / 1000000000) ≤ -Real.log (320 / 421) ∧
    -Real.log (320 / 421) ≤ (137155919 / 500000000) := by
  have h := checkLog_sound (w := (101 / 741)) (n := 12)
    (lo := (274311837 / 1000000000)) (hi := (137155919 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((421 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(421 / 320) = 1/(320 / 421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (274311837 / 1000000000) (137155919 / 500000000) (Real.log (421 / 320)) := by
  have h := reflection_log_1_neg
  have he : Real.log (421 / 320) = -Real.log (320 / 421) := by
    rw [show ((421 / 320) : ℝ) = ((320 / 421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (75849853 / 200000000) ≤ -Real.log (219 / 320) ∧
    -Real.log (219 / 320) ≤ (189624633 / 500000000) := by
  have h := checkLog_sound (w := (101 / 539)) (n := 12)
    (lo := (75849853 / 200000000)) (hi := (189624633 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 219) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 219) = 1/(219 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-189624633 / 500000000) (-75849853 / 200000000) (Real.log (219 / 320)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (27386637 / 100000000) ≤ -Real.log (5120 / 6733) ∧
    -Real.log (5120 / 6733) ≤ (273866371 / 1000000000) := by
  have h := checkLog_sound (w := (1613 / 11853)) (n := 12)
    (lo := (27386637 / 100000000)) (hi := (273866371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6733 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6733 / 5120) = 1/(5120 / 6733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (27386637 / 100000000) (273866371 / 1000000000) (Real.log (6733 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6733 / 5120) = -Real.log (5120 / 6733) := by
    rw [show ((6733 / 5120) : ℝ) = ((5120 / 6733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (378393467 / 1000000000) ≤ -Real.log (3507 / 5120) ∧
    -Real.log (3507 / 5120) ≤ (94598367 / 250000000) := by
  have h := checkLog_sound (w := (1613 / 8627)) (n := 12)
    (lo := (378393467 / 1000000000)) (hi := (94598367 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3507) = 1/(3507 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-94598367 / 250000000) (-378393467 / 1000000000) (Real.log (3507 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (201901119 / 1000000000) ≤ -Real.log (1000000 / 1223727) ∧
    -Real.log (1000000 / 1223727) ≤ (630941 / 3125000) := by
  have h := checkLog_sound (w := (223727 / 2223727)) (n := 12)
    (lo := (201901119 / 1000000000)) (hi := (630941 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1223727 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1223727 / 1000000) = 1/(1000000 / 1223727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (201901119 / 1000000000) (630941 / 3125000) (Real.log (1223727 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1223727 / 1000000) = -Real.log (1000000 / 1223727) := by
    rw [show ((1223727 / 1000000) : ℝ) = ((1000000 / 1223727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (31656377 / 125000000) ≤ -Real.log (776273 / 1000000) ∧
    -Real.log (776273 / 1000000) ≤ (253251017 / 1000000000) := by
  have h := checkLog_sound (w := (223727 / 1776273)) (n := 12)
    (lo := (31656377 / 125000000)) (hi := (253251017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 776273) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 776273) = 1/(776273 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-253251017 / 1000000000) (-31656377 / 125000000) (Real.log (776273 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (202245091 / 1000000000) ≤ -Real.log (250000 / 306037) ∧
    -Real.log (250000 / 306037) ≤ (50561273 / 250000000) := by
  have h := checkLog_sound (w := (56037 / 556037)) (n := 12)
    (lo := (202245091 / 1000000000)) (hi := (50561273 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((306037 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(306037 / 250000) = 1/(250000 / 306037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (202245091 / 1000000000) (50561273 / 250000000) (Real.log (306037 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (306037 / 250000) = -Real.log (250000 / 306037) := by
    rw [show ((306037 / 250000) : ℝ) = ((250000 / 306037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (126896749 / 500000000) ≤ -Real.log (193963 / 250000) ∧
    -Real.log (193963 / 250000) ≤ (253793499 / 1000000000) := by
  have h := checkLog_sound (w := (56037 / 443963)) (n := 12)
    (lo := (126896749 / 500000000)) (hi := (253793499 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 193963) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 193963) = 1/(193963 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-253793499 / 1000000000) (-126896749 / 500000000) (Real.log (193963 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (29757091 / 200000000) ≤ -Real.log (125000 / 145053) ∧
    -Real.log (125000 / 145053) ≤ (9299091 / 62500000) := by
  have h := checkLog_sound (w := (20053 / 270053)) (n := 12)
    (lo := (29757091 / 200000000)) (hi := (9299091 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145053 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145053 / 125000) = 1/(125000 / 145053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (29757091 / 200000000) (9299091 / 62500000) (Real.log (145053 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (145053 / 125000) = -Real.log (125000 / 145053) := by
    rw [show ((145053 / 125000) : ℝ) = ((125000 / 145053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (43714569 / 250000000) ≤ -Real.log (104947 / 125000) ∧
    -Real.log (104947 / 125000) ≤ (174858277 / 1000000000) := by
  have h := checkLog_sound (w := (20053 / 229947)) (n := 12)
    (lo := (43714569 / 250000000)) (hi := (174858277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 104947) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 104947) = 1/(104947 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-174858277 / 1000000000) (-43714569 / 250000000) (Real.log (104947 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (149052563 / 1000000000) ≤ -Real.log (500000 / 580367) ∧
    -Real.log (500000 / 580367) ≤ (37263141 / 250000000) := by
  have h := checkLog_sound (w := (80367 / 1080367)) (n := 12)
    (lo := (149052563 / 1000000000)) (hi := (37263141 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((580367 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(580367 / 500000) = 1/(500000 / 580367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (149052563 / 1000000000) (37263141 / 250000000) (Real.log (580367 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (580367 / 500000) = -Real.log (500000 / 580367) := by
    rw [show ((580367 / 500000) : ℝ) = ((500000 / 580367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (87613789 / 500000000) ≤ -Real.log (419633 / 500000) ∧
    -Real.log (419633 / 500000) ≤ (175227579 / 1000000000) := by
  have h := checkLog_sound (w := (80367 / 919633)) (n := 12)
    (lo := (87613789 / 500000000)) (hi := (175227579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 419633) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 419633) = 1/(419633 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-175227579 / 1000000000) (-87613789 / 500000000) (Real.log (419633 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (326129919 / 500000000) ≤ -Real.log (3125000000 / 5999607927) ∧
    -Real.log (3125000000 / 5999607927) ≤ (652259839 / 1000000000) := by
  have h := checkLog_sound (w := (2874607927 / 9124607927)) (n := 12)
    (lo := (326129919 / 500000000)) (hi := (652259839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5999607927 / 3125000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5999607927 / 3125000000) = 1/(3125000000 / 5999607927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (326129919 / 500000000) (652259839 / 1000000000) (Real.log (5999607927 / 3125000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (5999607927 / 3125000000) = -Real.log (3125000000 / 5999607927) := by
    rw [show ((5999607927 / 3125000000) : ℝ) = ((3125000000 / 5999607927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (653561103 / 1000000000) ≤ -Real.log (125000000000 / 240296803653) ∧
    -Real.log (125000000000 / 240296803653) ≤ (40847569 / 62500000) := by
  have h := checkLog_sound (w := (115296803653 / 365296803653)) (n := 12)
    (lo := (653561103 / 1000000000)) (hi := (40847569 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((240296803653 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(240296803653 / 125000000000) = 1/(125000000000 / 240296803653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (653561103 / 1000000000) (40847569 / 62500000) (Real.log (240296803653 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (240296803653 / 125000000000) = -Real.log (125000000000 / 240296803653) := by
    rw [show ((240296803653 / 125000000000) : ℝ) = ((125000000000 / 240296803653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (56894017 / 125000000) ≤ -Real.log (500000000000 / 788206597421) ∧
    -Real.log (500000000000 / 788206597421) ≤ (455152137 / 1000000000) := by
  have h := checkLog_sound (w := (288206597421 / 1288206597421)) (n := 12)
    (lo := (56894017 / 125000000)) (hi := (455152137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((788206597421 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(788206597421 / 500000000000) = 1/(500000000000 / 788206597421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (56894017 / 125000000) (455152137 / 1000000000) (Real.log (788206597421 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (788206597421 / 500000000000) = -Real.log (500000000000 / 788206597421) := by
    rw [show ((788206597421 / 500000000000) : ℝ) = ((500000000000 / 788206597421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (45603859 / 100000000) ≤ -Real.log (25000000000 / 39445280801) ∧
    -Real.log (25000000000 / 39445280801) ≤ (456038591 / 1000000000) := by
  have h := checkLog_sound (w := (14445280801 / 64445280801)) (n := 12)
    (lo := (45603859 / 100000000)) (hi := (456038591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39445280801 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39445280801 / 25000000000) = 1/(25000000000 / 39445280801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (45603859 / 100000000) (456038591 / 1000000000) (Real.log (39445280801 / 25000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (39445280801 / 25000000000) = -Real.log (25000000000 / 39445280801) := by
    rw [show ((39445280801 / 25000000000) : ℝ) = ((25000000000 / 39445280801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (80910933 / 250000000) ≤ -Real.log (500000000000 / 691077400973) ∧
    -Real.log (500000000000 / 691077400973) ≤ (323643733 / 1000000000) := by
  have h := checkLog_sound (w := (191077400973 / 1191077400973)) (n := 12)
    (lo := (80910933 / 250000000)) (hi := (323643733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((691077400973 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(691077400973 / 500000000000) = 1/(500000000000 / 691077400973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (80910933 / 250000000) (323643733 / 1000000000) (Real.log (691077400973 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (691077400973 / 500000000000) = -Real.log (500000000000 / 691077400973) := by
    rw [show ((691077400973 / 500000000000) : ℝ) = ((500000000000 / 691077400973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (162140071 / 500000000) ≤ -Real.log (100000000000 / 138303469937) ∧
    -Real.log (100000000000 / 138303469937) ≤ (324280143 / 1000000000) := by
  have h := checkLog_sound (w := (38303469937 / 238303469937)) (n := 12)
    (lo := (162140071 / 500000000)) (hi := (324280143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((138303469937 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(138303469937 / 100000000000) = 1/(100000000000 / 138303469937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (162140071 / 500000000) (324280143 / 1000000000) (Real.log (138303469937 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (138303469937 / 100000000000) = -Real.log (100000000000 / 138303469937) := by
    rw [show ((138303469937 / 100000000000) : ℝ) = ((100000000000 / 138303469937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (5235003 / 200000000) ≤ -Real.log (243541145311 / 250000000000) ∧
    -Real.log (243541145311 / 250000000000) ≤ (3271877 / 125000000) := by
  have h := checkLog_sound (w := (6458854689 / 493541145311)) (n := 12)
    (lo := (5235003 / 200000000)) (hi := (3271877 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243541145311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243541145311) = 1/(243541145311 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-3271877 / 125000000) (-5235003 / 200000000) (Real.log (243541145311 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (1303641 / 50000000) ≤ -Real.log (15222877191 / 15625000000) ∧
    -Real.log (15222877191 / 15625000000) ≤ (26072821 / 1000000000) := by
  have h := checkLog_sound (w := (402122809 / 30847877191)) (n := 12)
    (lo := (1303641 / 50000000)) (hi := (26072821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15222877191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15222877191) = 1/(15222877191 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-26072821 / 1000000000) (-1303641 / 50000000) (Real.log (15222877191 / 15625000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell111

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell112Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell112
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

theorem reflection_log_1_neg : (137378553 / 500000000) ≤ -Real.log (5120 / 6739) ∧
    -Real.log (5120 / 6739) ≤ (274757107 / 1000000000) := by
  have h := checkLog_sound (w := (1619 / 11859)) (n := 12)
    (lo := (137378553 / 500000000)) (hi := (274757107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6739 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6739 / 5120) = 1/(5120 / 6739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (137378553 / 500000000) (274757107 / 1000000000) (Real.log (6739 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6739 / 5120) = -Real.log (5120 / 6739) := by
    rw [show ((6739 / 5120) : ℝ) = ((5120 / 6739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (380105797 / 1000000000) ≤ -Real.log (3501 / 5120) ∧
    -Real.log (3501 / 5120) ≤ (190052899 / 500000000) := by
  have h := checkLog_sound (w := (1619 / 8621)) (n := 12)
    (lo := (380105797 / 1000000000)) (hi := (190052899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3501) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3501) = 1/(3501 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-190052899 / 500000000) (-380105797 / 1000000000) (Real.log (3501 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (274311837 / 1000000000) ≤ -Real.log (320 / 421) ∧
    -Real.log (320 / 421) ≤ (137155919 / 500000000) := by
  have h := checkLog_sound (w := (101 / 741)) (n := 12)
    (lo := (274311837 / 1000000000)) (hi := (137155919 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((421 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(421 / 320) = 1/(320 / 421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (274311837 / 1000000000) (137155919 / 500000000) (Real.log (421 / 320)) := by
  have h := reflection_log_3_neg
  have he : Real.log (421 / 320) = -Real.log (320 / 421) := by
    rw [show ((421 / 320) : ℝ) = ((320 / 421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (75849853 / 200000000) ≤ -Real.log (219 / 320) ∧
    -Real.log (219 / 320) ≤ (189624633 / 500000000) := by
  have h := checkLog_sound (w := (101 / 539)) (n := 12)
    (lo := (75849853 / 200000000)) (hi := (189624633 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 219) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 219) = 1/(219 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-189624633 / 500000000) (-75849853 / 200000000) (Real.log (219 / 320)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (101122137 / 500000000) ≤ -Real.log (1000000 / 1224147) ∧
    -Real.log (1000000 / 1224147) ≤ (8089771 / 40000000) := by
  have h := checkLog_sound (w := (224147 / 2224147)) (n := 12)
    (lo := (101122137 / 500000000)) (hi := (8089771 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1224147 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1224147 / 1000000) = 1/(1000000 / 1224147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (101122137 / 500000000) (8089771 / 40000000) (Real.log (1224147 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1224147 / 1000000) = -Real.log (1000000 / 1224147) := by
    rw [show ((1224147 / 1000000) : ℝ) = ((1000000 / 1224147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (253792209 / 1000000000) ≤ -Real.log (775853 / 1000000) ∧
    -Real.log (775853 / 1000000) ≤ (25379221 / 100000000) := by
  have h := checkLog_sound (w := (224147 / 1775853)) (n := 12)
    (lo := (253792209 / 1000000000)) (hi := (25379221 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 775853) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 775853) = 1/(775853 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-25379221 / 100000000) (-253792209 / 1000000000) (Real.log (775853 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (6330879 / 31250000) ≤ -Real.log (125000 / 153071) ∧
    -Real.log (125000 / 153071) ≤ (202588129 / 1000000000) := by
  have h := checkLog_sound (w := (28071 / 278071)) (n := 12)
    (lo := (6330879 / 31250000)) (hi := (202588129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153071 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153071 / 125000) = 1/(125000 / 153071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (6330879 / 31250000) (202588129 / 1000000000) (Real.log (153071 / 125000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (153071 / 125000) = -Real.log (125000 / 153071) := by
    rw [show ((153071 / 125000) : ℝ) = ((125000 / 153071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (50866997 / 200000000) ≤ -Real.log (96929 / 125000) ∧
    -Real.log (96929 / 125000) ≤ (127167493 / 500000000) := by
  have h := checkLog_sound (w := (28071 / 221929)) (n := 12)
    (lo := (50866997 / 200000000)) (hi := (127167493 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 96929) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 96929) = 1/(96929 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-127167493 / 500000000) (-50866997 / 200000000) (Real.log (96929 / 125000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (74525851 / 500000000) ≤ -Real.log (1000000 / 1160733) ∧
    -Real.log (1000000 / 1160733) ≤ (149051703 / 1000000000) := by
  have h := checkLog_sound (w := (160733 / 2160733)) (n := 12)
    (lo := (74525851 / 500000000)) (hi := (149051703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1160733 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1160733 / 1000000) = 1/(1000000 / 1160733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (74525851 / 500000000) (149051703 / 1000000000) (Real.log (1160733 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1160733 / 1000000) = -Real.log (1000000 / 1160733) := by
    rw [show ((1160733 / 1000000) : ℝ) = ((1000000 / 1160733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (175226387 / 1000000000) ≤ -Real.log (839267 / 1000000) ∧
    -Real.log (839267 / 1000000) ≤ (43806597 / 250000000) := by
  have h := checkLog_sound (w := (160733 / 1839267)) (n := 12)
    (lo := (175226387 / 1000000000)) (hi := (43806597 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 839267) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 839267) = 1/(839267 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-43806597 / 250000000) (-175226387 / 1000000000) (Real.log (839267 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (373299 / 2500000) ≤ -Real.log (250000 / 290261) ∧
    -Real.log (250000 / 290261) ≤ (149319601 / 1000000000) := by
  have h := checkLog_sound (w := (40261 / 540261)) (n := 12)
    (lo := (373299 / 2500000)) (hi := (149319601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((290261 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(290261 / 250000) = 1/(250000 / 290261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (373299 / 2500000) (149319601 / 1000000000) (Real.log (290261 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (290261 / 250000) = -Real.log (250000 / 290261) := by
    rw [show ((290261 / 250000) : ℝ) = ((250000 / 290261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (175597017 / 1000000000) ≤ -Real.log (209739 / 250000) ∧
    -Real.log (209739 / 250000) ≤ (87798509 / 500000000) := by
  have h := checkLog_sound (w := (40261 / 459739)) (n := 12)
    (lo := (175597017 / 1000000000)) (hi := (87798509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 209739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 209739) = 1/(209739 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-87798509 / 500000000) (-175597017 / 1000000000) (Real.log (209739 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (653561103 / 1000000000) ≤ -Real.log (500000000000 / 961187214611) ∧
    -Real.log (500000000000 / 961187214611) ≤ (40847569 / 62500000) := by
  have h := checkLog_sound (w := (461187214611 / 1461187214611)) (n := 12)
    (lo := (653561103 / 1000000000)) (hi := (40847569 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((961187214611 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(961187214611 / 500000000000) = 1/(500000000000 / 961187214611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (653561103 / 1000000000) (40847569 / 62500000) (Real.log (961187214611 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (961187214611 / 500000000000) = -Real.log (500000000000 / 961187214611) := by
    rw [show ((961187214611 / 500000000000) : ℝ) = ((500000000000 / 961187214611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (654862903 / 1000000000) ≤ -Real.log (500000000000 / 962439303057) ∧
    -Real.log (500000000000 / 962439303057) ≤ (81857863 / 125000000) := by
  have h := checkLog_sound (w := (462439303057 / 1462439303057)) (n := 12)
    (lo := (654862903 / 1000000000)) (hi := (81857863 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((962439303057 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(962439303057 / 500000000000) = 1/(500000000000 / 962439303057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (654862903 / 1000000000) (81857863 / 125000000) (Real.log (962439303057 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (962439303057 / 500000000000) = -Real.log (500000000000 / 962439303057) := by
    rw [show ((962439303057 / 500000000000) : ℝ) = ((500000000000 / 962439303057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (114009121 / 250000000) ≤ -Real.log (62500000000 / 98612994343) ∧
    -Real.log (62500000000 / 98612994343) ≤ (91207297 / 200000000) := by
  have h := checkLog_sound (w := (36112994343 / 161112994343)) (n := 12)
    (lo := (114009121 / 250000000)) (hi := (91207297 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98612994343 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98612994343 / 62500000000) = 1/(62500000000 / 98612994343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (114009121 / 250000000) (91207297 / 200000000) (Real.log (98612994343 / 62500000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (98612994343 / 62500000000) = -Real.log (62500000000 / 98612994343) := by
    rw [show ((98612994343 / 62500000000) : ℝ) = ((62500000000 / 98612994343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (228461557 / 500000000) ≤ -Real.log (250000000000 / 394801865283) ∧
    -Real.log (250000000000 / 394801865283) ≤ (91384623 / 200000000) := by
  have h := checkLog_sound (w := (144801865283 / 644801865283)) (n := 12)
    (lo := (228461557 / 500000000)) (hi := (91384623 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((394801865283 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(394801865283 / 250000000000) = 1/(250000000000 / 394801865283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (228461557 / 500000000) (91384623 / 200000000) (Real.log (394801865283 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (394801865283 / 250000000000) = -Real.log (250000000000 / 394801865283) := by
    rw [show ((394801865283 / 250000000000) : ℝ) = ((250000000000 / 394801865283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (324278089 / 1000000000) ≤ -Real.log (125000000000 / 172878982493) ∧
    -Real.log (125000000000 / 172878982493) ≤ (32427809 / 100000000) := by
  have h := checkLog_sound (w := (47878982493 / 297878982493)) (n := 12)
    (lo := (324278089 / 1000000000)) (hi := (32427809 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((172878982493 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(172878982493 / 125000000000) = 1/(125000000000 / 172878982493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (324278089 / 1000000000) (32427809 / 100000000) (Real.log (172878982493 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (172878982493 / 125000000000) = -Real.log (125000000000 / 172878982493) := by
    rw [show ((172878982493 / 125000000000) : ℝ) = ((125000000000 / 172878982493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (324916617 / 1000000000) ≤ -Real.log (500000000000 / 691957623523) ∧
    -Real.log (500000000000 / 691957623523) ≤ (162458309 / 500000000) := by
  have h := checkLog_sound (w := (191957623523 / 1191957623523)) (n := 12)
    (lo := (324916617 / 1000000000)) (hi := (162458309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((691957623523 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(691957623523 / 500000000000) = 1/(500000000000 / 691957623523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (324916617 / 1000000000) (162458309 / 500000000) (Real.log (691957623523 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (691957623523 / 500000000000) = -Real.log (500000000000 / 691957623523) := by
    rw [show ((691957623523 / 500000000000) : ℝ) = ((500000000000 / 691957623523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3284677 / 125000000) ≤ -Real.log (60879051879 / 62500000000) ∧
    -Real.log (60879051879 / 62500000000) ≤ (26277417 / 1000000000) := by
  have h := checkLog_sound (w := (1620948121 / 123379051879)) (n := 12)
    (lo := (3284677 / 125000000)) (hi := (26277417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60879051879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60879051879) = 1/(60879051879 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-26277417 / 1000000000) (-3284677 / 125000000) (Real.log (60879051879 / 62500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (5234937 / 200000000) ≤ -Real.log (974164902711 / 1000000000000) ∧
    -Real.log (974164902711 / 1000000000000) ≤ (13087343 / 500000000) := by
  have h := checkLog_sound (w := (25835097289 / 1974164902711)) (n := 12)
    (lo := (5234937 / 200000000)) (hi := (13087343 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 974164902711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 974164902711) = 1/(974164902711 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-13087343 / 500000000) (-5234937 / 200000000) (Real.log (974164902711 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell112

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell113Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell113
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

theorem reflection_log_1_neg : (275202177 / 1000000000) ≤ -Real.log (2560 / 3371) ∧
    -Real.log (2560 / 3371) ≤ (137601089 / 500000000) := by
  have h := checkLog_sound (w := (811 / 5931)) (n := 12)
    (lo := (275202177 / 1000000000)) (hi := (137601089 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3371 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3371 / 2560) = 1/(2560 / 3371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (275202177 / 1000000000) (137601089 / 500000000) (Real.log (3371 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3371 / 2560) = -Real.log (2560 / 3371) := by
    rw [show ((3371 / 2560) : ℝ) = ((2560 / 3371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (190481531 / 500000000) ≤ -Real.log (1749 / 2560) ∧
    -Real.log (1749 / 2560) ≤ (380963063 / 1000000000) := by
  have h := checkLog_sound (w := (811 / 4309)) (n := 12)
    (lo := (190481531 / 500000000)) (hi := (380963063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1749) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1749) = 1/(1749 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-380963063 / 1000000000) (-190481531 / 500000000) (Real.log (1749 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (137378553 / 500000000) ≤ -Real.log (5120 / 6739) ∧
    -Real.log (5120 / 6739) ≤ (274757107 / 1000000000) := by
  have h := checkLog_sound (w := (1619 / 11859)) (n := 12)
    (lo := (137378553 / 500000000)) (hi := (274757107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6739 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6739 / 5120) = 1/(5120 / 6739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (137378553 / 500000000) (274757107 / 1000000000) (Real.log (6739 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6739 / 5120) = -Real.log (5120 / 6739) := by
    rw [show ((6739 / 5120) : ℝ) = ((5120 / 6739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (380105797 / 1000000000) ≤ -Real.log (3501 / 5120) ∧
    -Real.log (3501 / 5120) ≤ (190052899 / 500000000) := by
  have h := checkLog_sound (w := (1619 / 8621)) (n := 12)
    (lo := (380105797 / 1000000000)) (hi := (190052899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3501) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3501) = 1/(3501 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-190052899 / 500000000) (-380105797 / 1000000000) (Real.log (3501 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (12661707 / 62500000) ≤ -Real.log (1000000 / 1224567) ∧
    -Real.log (1000000 / 1224567) ≤ (202587313 / 1000000000) := by
  have h := checkLog_sound (w := (224567 / 2224567)) (n := 12)
    (lo := (12661707 / 62500000)) (hi := (202587313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1224567 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1224567 / 1000000) = 1/(1000000 / 1224567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (12661707 / 62500000) (202587313 / 1000000000) (Real.log (1224567 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1224567 / 1000000) = -Real.log (1000000 / 1224567) := by
    rw [show ((1224567 / 1000000) : ℝ) = ((1000000 / 1224567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (50866739 / 200000000) ≤ -Real.log (775433 / 1000000) ∧
    -Real.log (775433 / 1000000) ≤ (993491 / 3906250) := by
  have h := checkLog_sound (w := (224567 / 1775433)) (n := 12)
    (lo := (50866739 / 200000000)) (hi := (993491 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 775433) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 775433) = 1/(775433 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-993491 / 3906250) (-50866739 / 200000000) (Real.log (775433 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (25366381 / 125000000) ≤ -Real.log (250000 / 306247) ∧
    -Real.log (250000 / 306247) ≤ (202931049 / 1000000000) := by
  have h := checkLog_sound (w := (56247 / 556247)) (n := 12)
    (lo := (25366381 / 125000000)) (hi := (202931049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((306247 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(306247 / 250000) = 1/(250000 / 306247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (25366381 / 125000000) (202931049 / 1000000000) (Real.log (306247 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (306247 / 250000) = -Real.log (250000 / 306247) := by
    rw [show ((306247 / 250000) : ℝ) = ((250000 / 306247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (50975353 / 200000000) ≤ -Real.log (193753 / 250000) ∧
    -Real.log (193753 / 250000) ≤ (127438383 / 500000000) := by
  have h := checkLog_sound (w := (56247 / 443753)) (n := 12)
    (lo := (50975353 / 200000000)) (hi := (127438383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 193753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 193753) = 1/(193753 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-127438383 / 500000000) (-50975353 / 200000000) (Real.log (193753 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (149318739 / 1000000000) ≤ -Real.log (1000000 / 1161043) ∧
    -Real.log (1000000 / 1161043) ≤ (7465937 / 50000000) := by
  have h := checkLog_sound (w := (161043 / 2161043)) (n := 12)
    (lo := (149318739 / 1000000000)) (hi := (7465937 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1161043 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1161043 / 1000000) = 1/(1000000 / 1161043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (149318739 / 1000000000) (7465937 / 50000000) (Real.log (1161043 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1161043 / 1000000) = -Real.log (1000000 / 1161043) := by
    rw [show ((1161043 / 1000000) : ℝ) = ((1000000 / 1161043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (7023833 / 40000000) ≤ -Real.log (838957 / 1000000) ∧
    -Real.log (838957 / 1000000) ≤ (87797913 / 500000000) := by
  have h := checkLog_sound (w := (161043 / 1838957)) (n := 12)
    (lo := (7023833 / 40000000)) (hi := (87797913 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 838957) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 838957) = 1/(838957 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-87797913 / 500000000) (-7023833 / 40000000) (Real.log (838957 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (29917313 / 200000000) ≤ -Real.log (500000 / 580677) ∧
    -Real.log (500000 / 580677) ≤ (74793283 / 500000000) := by
  have h := checkLog_sound (w := (80677 / 1080677)) (n := 12)
    (lo := (29917313 / 200000000)) (hi := (74793283 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((580677 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(580677 / 500000) = 1/(500000 / 580677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (29917313 / 200000000) (74793283 / 500000000) (Real.log (580677 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (580677 / 500000) = -Real.log (500000 / 580677) := by
    rw [show ((580677 / 500000) : ℝ) = ((500000 / 580677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1374739 / 7812500) ≤ -Real.log (419323 / 500000) ∧
    -Real.log (419323 / 500000) ≤ (175966593 / 1000000000) := by
  have h := checkLog_sound (w := (80677 / 919323)) (n := 12)
    (lo := (1374739 / 7812500)) (hi := (175966593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 419323) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 419323) = 1/(419323 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-175966593 / 1000000000) (-1374739 / 7812500) (Real.log (419323 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (654862903 / 1000000000) ≤ -Real.log (31250000000 / 60152456441) ∧
    -Real.log (31250000000 / 60152456441) ≤ (81857863 / 125000000) := by
  have h := checkLog_sound (w := (28902456441 / 91402456441)) (n := 12)
    (lo := (654862903 / 1000000000)) (hi := (81857863 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60152456441 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60152456441 / 31250000000) = 1/(31250000000 / 60152456441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (654862903 / 1000000000) (81857863 / 125000000) (Real.log (60152456441 / 31250000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (60152456441 / 31250000000) = -Real.log (31250000000 / 60152456441) := by
    rw [show ((60152456441 / 31250000000) : ℝ) = ((31250000000 / 60152456441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (16404131 / 25000000) ≤ -Real.log (250000000000 / 481846769583) ∧
    -Real.log (250000000000 / 481846769583) ≤ (656165241 / 1000000000) := by
  have h := checkLog_sound (w := (231846769583 / 731846769583)) (n := 12)
    (lo := (16404131 / 25000000)) (hi := (656165241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((481846769583 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(481846769583 / 250000000000) = 1/(250000000000 / 481846769583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (16404131 / 25000000) (656165241 / 1000000000) (Real.log (481846769583 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (481846769583 / 250000000000) = -Real.log (250000000000 / 481846769583) := by
    rw [show ((481846769583 / 250000000000) : ℝ) = ((250000000000 / 481846769583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (28557563 / 62500000) ≤ -Real.log (50000000000 / 78960206749) ∧
    -Real.log (50000000000 / 78960206749) ≤ (456921009 / 1000000000) := by
  have h := checkLog_sound (w := (28960206749 / 128960206749)) (n := 12)
    (lo := (28557563 / 62500000)) (hi := (456921009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78960206749 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78960206749 / 50000000000) = 1/(50000000000 / 78960206749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (28557563 / 62500000) (456921009 / 1000000000) (Real.log (78960206749 / 50000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (78960206749 / 50000000000) = -Real.log (50000000000 / 78960206749) := by
    rw [show ((78960206749 / 50000000000) : ℝ) = ((50000000000 / 78960206749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (457807813 / 1000000000) ≤ -Real.log (500000000000 / 790302601767) ∧
    -Real.log (500000000000 / 790302601767) ≤ (228903907 / 500000000) := by
  have h := checkLog_sound (w := (290302601767 / 1290302601767)) (n := 12)
    (lo := (457807813 / 1000000000)) (hi := (228903907 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((790302601767 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(790302601767 / 500000000000) = 1/(500000000000 / 790302601767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (457807813 / 1000000000) (228903907 / 500000000) (Real.log (790302601767 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (790302601767 / 500000000000) = -Real.log (500000000000 / 790302601767) := by
    rw [show ((790302601767 / 500000000000) : ℝ) = ((500000000000 / 790302601767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (81228641 / 250000000) ≤ -Real.log (500000000000 / 691956202761) ∧
    -Real.log (500000000000 / 691956202761) ≤ (64982913 / 200000000) := by
  have h := checkLog_sound (w := (191956202761 / 1191956202761)) (n := 12)
    (lo := (81228641 / 250000000)) (hi := (64982913 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((691956202761 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(691956202761 / 500000000000) = 1/(500000000000 / 691956202761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (81228641 / 250000000) (64982913 / 200000000) (Real.log (691956202761 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (691956202761 / 500000000000) = -Real.log (500000000000 / 691956202761) := by
    rw [show ((691956202761 / 500000000000) : ℝ) = ((500000000000 / 691956202761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (162776579 / 500000000) ≤ -Real.log (10000000000 / 13847964457) ∧
    -Real.log (10000000000 / 13847964457) ≤ (325553159 / 1000000000) := by
  have h := checkLog_sound (w := (3847964457 / 23847964457)) (n := 12)
    (lo := (162776579 / 500000000)) (hi := (325553159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13847964457 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13847964457 / 10000000000) = 1/(10000000000 / 13847964457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (162776579 / 500000000) (325553159 / 1000000000) (Real.log (13847964457 / 10000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (13847964457 / 10000000000) = -Real.log (10000000000 / 13847964457) := by
    rw [show ((13847964457 / 10000000000) : ℝ) = ((10000000000 / 13847964457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (13190013 / 500000000) ≤ -Real.log (243491221671 / 250000000000) ∧
    -Real.log (243491221671 / 250000000000) ≤ (26380027 / 1000000000) := by
  have h := checkLog_sound (w := (6508778329 / 493491221671)) (n := 12)
    (lo := (13190013 / 500000000)) (hi := (26380027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243491221671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243491221671) = 1/(243491221671 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-26380027 / 1000000000) (-13190013 / 500000000) (Real.log (243491221671 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (13138543 / 500000000) ≤ -Real.log (974065152151 / 1000000000000) ∧
    -Real.log (974065152151 / 1000000000000) ≤ (26277087 / 1000000000) := by
  have h := checkLog_sound (w := (25934847849 / 1974065152151)) (n := 12)
    (lo := (13138543 / 500000000)) (hi := (26277087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 974065152151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 974065152151) = 1/(974065152151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-26277087 / 1000000000) (-13138543 / 500000000) (Real.log (974065152151 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell113

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell114Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell114
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

theorem reflection_log_1_neg : (5512941 / 20000000) ≤ -Real.log (1024 / 1349) ∧
    -Real.log (1024 / 1349) ≤ (275647051 / 1000000000) := by
  have h := checkLog_sound (w := (325 / 2373)) (n := 12)
    (lo := (5512941 / 20000000)) (hi := (275647051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1349 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1349 / 1024) = 1/(1024 / 1349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (5512941 / 20000000) (275647051 / 1000000000) (Real.log (1349 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1349 / 1024) = -Real.log (1024 / 1349) := by
    rw [show ((1349 / 1024) : ℝ) = ((1024 / 1349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (381821063 / 1000000000) ≤ -Real.log (699 / 1024) ∧
    -Real.log (699 / 1024) ≤ (47727633 / 125000000) := by
  have h := checkLog_sound (w := (325 / 1723)) (n := 12)
    (lo := (381821063 / 1000000000)) (hi := (47727633 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 699) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 699) = 1/(699 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-47727633 / 125000000) (-381821063 / 1000000000) (Real.log (699 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (275202177 / 1000000000) ≤ -Real.log (2560 / 3371) ∧
    -Real.log (2560 / 3371) ≤ (137601089 / 500000000) := by
  have h := checkLog_sound (w := (811 / 5931)) (n := 12)
    (lo := (275202177 / 1000000000)) (hi := (137601089 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3371 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3371 / 2560) = 1/(2560 / 3371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (275202177 / 1000000000) (137601089 / 500000000) (Real.log (3371 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3371 / 2560) = -Real.log (2560 / 3371) := by
    rw [show ((3371 / 2560) : ℝ) = ((2560 / 3371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (190481531 / 500000000) ≤ -Real.log (1749 / 2560) ∧
    -Real.log (1749 / 2560) ≤ (380963063 / 1000000000) := by
  have h := checkLog_sound (w := (811 / 4309)) (n := 12)
    (lo := (190481531 / 500000000)) (hi := (380963063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1749) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1749) = 1/(1749 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-380963063 / 1000000000) (-190481531 / 500000000) (Real.log (1749 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (202930231 / 1000000000) ≤ -Real.log (1000000 / 1224987) ∧
    -Real.log (1000000 / 1224987) ≤ (25366279 / 125000000) := by
  have h := checkLog_sound (w := (224987 / 2224987)) (n := 12)
    (lo := (202930231 / 1000000000)) (hi := (25366279 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1224987 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1224987 / 1000000) = 1/(1000000 / 1224987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (202930231 / 1000000000) (25366279 / 125000000) (Real.log (1224987 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1224987 / 1000000) = -Real.log (1000000 / 1224987) := by
    rw [show ((1224987 / 1000000) : ℝ) = ((1000000 / 1224987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (10195019 / 40000000) ≤ -Real.log (775013 / 1000000) ∧
    -Real.log (775013 / 1000000) ≤ (63718869 / 250000000) := by
  have h := checkLog_sound (w := (224987 / 1775013)) (n := 12)
    (lo := (10195019 / 40000000)) (hi := (63718869 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 775013) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 775013) = 1/(775013 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-63718869 / 250000000) (-10195019 / 40000000) (Real.log (775013 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (203273033 / 1000000000) ≤ -Real.log (1000000 / 1225407) ∧
    -Real.log (1000000 / 1225407) ≤ (101636517 / 500000000) := by
  have h := checkLog_sound (w := (225407 / 2225407)) (n := 12)
    (lo := (203273033 / 1000000000)) (hi := (101636517 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1225407 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1225407 / 1000000) = 1/(1000000 / 1225407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (203273033 / 1000000000) (101636517 / 500000000) (Real.log (1225407 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1225407 / 1000000) = -Real.log (1000000 / 1225407) := by
    rw [show ((1225407 / 1000000) : ℝ) = ((1000000 / 1225407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (63854387 / 250000000) ≤ -Real.log (774593 / 1000000) ∧
    -Real.log (774593 / 1000000) ≤ (255417549 / 1000000000) := by
  have h := checkLog_sound (w := (225407 / 1774593)) (n := 12)
    (lo := (63854387 / 250000000)) (hi := (255417549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 774593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 774593) = 1/(774593 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-255417549 / 1000000000) (-63854387 / 250000000) (Real.log (774593 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (18698213 / 125000000) ≤ -Real.log (1000000 / 1161353) ∧
    -Real.log (1000000 / 1161353) ≤ (29917141 / 200000000) := by
  have h := checkLog_sound (w := (161353 / 2161353)) (n := 12)
    (lo := (18698213 / 125000000)) (hi := (29917141 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1161353 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1161353 / 1000000) = 1/(1000000 / 1161353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (18698213 / 125000000) (29917141 / 200000000) (Real.log (1161353 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1161353 / 1000000) = -Real.log (1000000 / 1161353) := by
    rw [show ((1161353 / 1000000) : ℝ) = ((1000000 / 1161353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (879827 / 5000000) ≤ -Real.log (838647 / 1000000) ∧
    -Real.log (838647 / 1000000) ≤ (175965401 / 1000000000) := by
  have h := checkLog_sound (w := (161353 / 1838647)) (n := 12)
    (lo := (879827 / 5000000)) (hi := (175965401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 838647) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 838647) = 1/(838647 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-175965401 / 1000000000) (-879827 / 5000000) (Real.log (838647 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (149852599 / 1000000000) ≤ -Real.log (1000000 / 1161663) ∧
    -Real.log (1000000 / 1161663) ≤ (749263 / 5000000) := by
  have h := checkLog_sound (w := (161663 / 2161663)) (n := 12)
    (lo := (149852599 / 1000000000)) (hi := (749263 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1161663 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1161663 / 1000000) = 1/(1000000 / 1161663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (149852599 / 1000000000) (749263 / 5000000) (Real.log (1161663 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1161663 / 1000000) = -Real.log (1000000 / 1161663) := by
    rw [show ((1161663 / 1000000) : ℝ) = ((1000000 / 1161663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (176335111 / 1000000000) ≤ -Real.log (838337 / 1000000) ∧
    -Real.log (838337 / 1000000) ≤ (22041889 / 125000000) := by
  have h := checkLog_sound (w := (161663 / 1838337)) (n := 12)
    (lo := (176335111 / 1000000000)) (hi := (22041889 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 838337) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 838337) = 1/(838337 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-22041889 / 125000000) (-176335111 / 1000000000) (Real.log (838337 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (16404131 / 25000000) ≤ -Real.log (100000000000 / 192738707833) ∧
    -Real.log (100000000000 / 192738707833) ≤ (656165241 / 1000000000) := by
  have h := checkLog_sound (w := (92738707833 / 292738707833)) (n := 12)
    (lo := (16404131 / 25000000)) (hi := (656165241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((192738707833 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(192738707833 / 100000000000) = 1/(100000000000 / 192738707833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (16404131 / 25000000) (656165241 / 1000000000) (Real.log (192738707833 / 100000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (192738707833 / 100000000000) = -Real.log (100000000000 / 192738707833) := by
    rw [show ((192738707833 / 100000000000) : ℝ) = ((100000000000 / 192738707833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (657468113 / 1000000000) ≤ -Real.log (50000000000 / 96494992847) ∧
    -Real.log (50000000000 / 96494992847) ≤ (328734057 / 500000000) := by
  have h := checkLog_sound (w := (46494992847 / 146494992847)) (n := 12)
    (lo := (657468113 / 1000000000)) (hi := (328734057 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((96494992847 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(96494992847 / 50000000000) = 1/(50000000000 / 96494992847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (657468113 / 1000000000) (328734057 / 500000000) (Real.log (96494992847 / 50000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (96494992847 / 50000000000) = -Real.log (50000000000 / 96494992847) := by
    rw [show ((96494992847 / 50000000000) : ℝ) = ((50000000000 / 96494992847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (457805707 / 1000000000) ≤ -Real.log (500000000000 / 790300936887) ∧
    -Real.log (500000000000 / 790300936887) ≤ (114451427 / 250000000) := by
  have h := checkLog_sound (w := (290300936887 / 1290300936887)) (n := 12)
    (lo := (457805707 / 1000000000)) (hi := (114451427 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((790300936887 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(790300936887 / 500000000000) = 1/(500000000000 / 790300936887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (457805707 / 1000000000) (114451427 / 250000000) (Real.log (790300936887 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (790300936887 / 500000000000) = -Real.log (500000000000 / 790300936887) := by
    rw [show ((790300936887 / 500000000000) : ℝ) = ((500000000000 / 790300936887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (229345291 / 500000000) ≤ -Real.log (62500000000 / 98875070521) ∧
    -Real.log (62500000000 / 98875070521) ≤ (458690583 / 1000000000) := by
  have h := checkLog_sound (w := (36375070521 / 161375070521)) (n := 12)
    (lo := (229345291 / 500000000)) (hi := (458690583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98875070521 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98875070521 / 62500000000) = 1/(62500000000 / 98875070521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (229345291 / 500000000) (458690583 / 1000000000) (Real.log (98875070521 / 62500000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (98875070521 / 62500000000) = -Real.log (62500000000 / 98875070521) := by
    rw [show ((98875070521 / 62500000000) : ℝ) = ((62500000000 / 98875070521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (635842 / 1953125) ≤ -Real.log (500000000000 / 692396801037) ∧
    -Real.log (500000000000 / 692396801037) ≤ (65110221 / 200000000) := by
  have h := checkLog_sound (w := (192396801037 / 1192396801037)) (n := 12)
    (lo := (635842 / 1953125)) (hi := (65110221 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((692396801037 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(692396801037 / 500000000000) = 1/(500000000000 / 692396801037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (635842 / 1953125) (65110221 / 200000000) (Real.log (692396801037 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (692396801037 / 500000000000) = -Real.log (500000000000 / 692396801037) := by
    rw [show ((692396801037 / 500000000000) : ℝ) = ((500000000000 / 692396801037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (32618771 / 100000000) ≤ -Real.log (125000000000 / 173209431291) ∧
    -Real.log (125000000000 / 173209431291) ≤ (326187711 / 1000000000) := by
  have h := checkLog_sound (w := (48209431291 / 298209431291)) (n := 12)
    (lo := (32618771 / 100000000)) (hi := (326187711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((173209431291 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(173209431291 / 125000000000) = 1/(125000000000 / 173209431291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (32618771 / 100000000) (326187711 / 1000000000) (Real.log (173209431291 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (173209431291 / 125000000000) = -Real.log (125000000000 / 173209431291) := by
    rw [show ((173209431291 / 125000000000) : ℝ) = ((125000000000 / 173209431291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1655157 / 62500000) ≤ -Real.log (973865074431 / 1000000000000) ∧
    -Real.log (973865074431 / 1000000000000) ≤ (26482513 / 1000000000) := by
  have h := checkLog_sound (w := (26134925569 / 1973865074431)) (n := 12)
    (lo := (1655157 / 62500000)) (hi := (26482513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 973865074431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 973865074431) = 1/(973865074431 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-26482513 / 1000000000) (-1655157 / 62500000) (Real.log (973865074431 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (5275939 / 200000000) ≤ -Real.log (973965209391 / 1000000000000) ∧
    -Real.log (973965209391 / 1000000000000) ≤ (1648731 / 62500000) := by
  have h := checkLog_sound (w := (26034790609 / 1973965209391)) (n := 12)
    (lo := (5275939 / 200000000)) (hi := (1648731 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 973965209391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 973965209391) = 1/(973965209391 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-1648731 / 62500000) (-5275939 / 200000000) (Real.log (973965209391 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell114

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell115Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell115
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

theorem reflection_log_1_neg : (11043669 / 40000000) ≤ -Real.log (1280 / 1687) ∧
    -Real.log (1280 / 1687) ≤ (138045863 / 500000000) := by
  have h := checkLog_sound (w := (407 / 2967)) (n := 12)
    (lo := (11043669 / 40000000)) (hi := (138045863 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1687 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1687 / 1280) = 1/(1280 / 1687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (11043669 / 40000000) (138045863 / 500000000) (Real.log (1687 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1687 / 1280) = -Real.log (1280 / 1687) := by
    rw [show ((1687 / 1280) : ℝ) = ((1280 / 1687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (382679801 / 1000000000) ≤ -Real.log (873 / 1280) ∧
    -Real.log (873 / 1280) ≤ (191339901 / 500000000) := by
  have h := checkLog_sound (w := (407 / 2153)) (n := 12)
    (lo := (382679801 / 1000000000)) (hi := (191339901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 873) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 873) = 1/(873 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-191339901 / 500000000) (-382679801 / 1000000000) (Real.log (873 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (5512941 / 20000000) ≤ -Real.log (1024 / 1349) ∧
    -Real.log (1024 / 1349) ≤ (275647051 / 1000000000) := by
  have h := checkLog_sound (w := (325 / 2373)) (n := 12)
    (lo := (5512941 / 20000000)) (hi := (275647051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1349 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1349 / 1024) = 1/(1024 / 1349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (5512941 / 20000000) (275647051 / 1000000000) (Real.log (1349 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1349 / 1024) = -Real.log (1024 / 1349) := by
    rw [show ((1349 / 1024) : ℝ) = ((1024 / 1349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (381821063 / 1000000000) ≤ -Real.log (699 / 1024) ∧
    -Real.log (699 / 1024) ≤ (47727633 / 125000000) := by
  have h := checkLog_sound (w := (325 / 1723)) (n := 12)
    (lo := (381821063 / 1000000000)) (hi := (47727633 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 699) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 699) = 1/(699 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-47727633 / 125000000) (-381821063 / 1000000000) (Real.log (699 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (203272217 / 1000000000) ≤ -Real.log (500000 / 612703) ∧
    -Real.log (500000 / 612703) ≤ (101636109 / 500000000) := by
  have h := checkLog_sound (w := (112703 / 1112703)) (n := 12)
    (lo := (203272217 / 1000000000)) (hi := (101636109 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((612703 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(612703 / 500000) = 1/(500000 / 612703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (203272217 / 1000000000) (101636109 / 500000000) (Real.log (612703 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (612703 / 500000) = -Real.log (500000 / 612703) := by
    rw [show ((612703 / 500000) : ℝ) = ((500000 / 612703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (255416257 / 1000000000) ≤ -Real.log (387297 / 500000) ∧
    -Real.log (387297 / 500000) ≤ (127708129 / 500000000) := by
  have h := checkLog_sound (w := (112703 / 887297)) (n := 12)
    (lo := (255416257 / 1000000000)) (hi := (127708129 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 387297) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 387297) = 1/(387297 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-127708129 / 500000000) (-255416257 / 1000000000) (Real.log (387297 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (101807859 / 500000000) ≤ -Real.log (1000000 / 1225827) ∧
    -Real.log (1000000 / 1225827) ≤ (203615719 / 1000000000) := by
  have h := checkLog_sound (w := (225827 / 2225827)) (n := 12)
    (lo := (101807859 / 500000000)) (hi := (203615719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1225827 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1225827 / 1000000) = 1/(1000000 / 1225827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (101807859 / 500000000) (203615719 / 1000000000) (Real.log (1225827 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1225827 / 1000000) = -Real.log (1000000 / 1225827) := by
    rw [show ((1225827 / 1000000) : ℝ) = ((1000000 / 1225827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (63989979 / 250000000) ≤ -Real.log (774173 / 1000000) ∧
    -Real.log (774173 / 1000000) ≤ (255959917 / 1000000000) := by
  have h := checkLog_sound (w := (225827 / 1774173)) (n := 12)
    (lo := (63989979 / 250000000)) (hi := (255959917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 774173) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 774173) = 1/(774173 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-255959917 / 1000000000) (-63989979 / 250000000) (Real.log (774173 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (74925869 / 500000000) ≤ -Real.log (500000 / 580831) ∧
    -Real.log (500000 / 580831) ≤ (149851739 / 1000000000) := by
  have h := checkLog_sound (w := (80831 / 1080831)) (n := 12)
    (lo := (74925869 / 500000000)) (hi := (149851739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((580831 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(580831 / 500000) = 1/(500000 / 580831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (74925869 / 500000000) (149851739 / 1000000000) (Real.log (580831 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (580831 / 500000) = -Real.log (500000 / 580831) := by
    rw [show ((580831 / 500000) : ℝ) = ((500000 / 580831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (88166959 / 500000000) ≤ -Real.log (419169 / 500000) ∧
    -Real.log (419169 / 500000) ≤ (176333919 / 1000000000) := by
  have h := checkLog_sound (w := (80831 / 919169)) (n := 12)
    (lo := (88166959 / 500000000)) (hi := (176333919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 419169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 419169) = 1/(419169 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-176333919 / 1000000000) (-88166959 / 500000000) (Real.log (419169 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (75059711 / 500000000) ≤ -Real.log (1000000 / 1161973) ∧
    -Real.log (1000000 / 1161973) ≤ (150119423 / 1000000000) := by
  have h := checkLog_sound (w := (161973 / 2161973)) (n := 12)
    (lo := (75059711 / 500000000)) (hi := (150119423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1161973 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1161973 / 1000000) = 1/(1000000 / 1161973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (75059711 / 500000000) (150119423 / 1000000000) (Real.log (1161973 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1161973 / 1000000) = -Real.log (1000000 / 1161973) := by
    rw [show ((1161973 / 1000000) : ℝ) = ((1000000 / 1161973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (176704959 / 1000000000) ≤ -Real.log (838027 / 1000000) ∧
    -Real.log (838027 / 1000000) ≤ (552203 / 3125000) := by
  have h := checkLog_sound (w := (161973 / 1838027)) (n := 12)
    (lo := (176704959 / 1000000000)) (hi := (552203 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 838027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 838027) = 1/(838027 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-552203 / 3125000) (-176704959 / 1000000000) (Real.log (838027 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (657468113 / 1000000000) ≤ -Real.log (500000000000 / 964949928469) ∧
    -Real.log (500000000000 / 964949928469) ≤ (328734057 / 500000000) := by
  have h := checkLog_sound (w := (464949928469 / 1464949928469)) (n := 12)
    (lo := (657468113 / 1000000000)) (hi := (328734057 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((964949928469 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(964949928469 / 500000000000) = 1/(500000000000 / 964949928469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (657468113 / 1000000000) (328734057 / 500000000) (Real.log (964949928469 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (964949928469 / 500000000000) = -Real.log (500000000000 / 964949928469) := by
    rw [show ((964949928469 / 500000000000) : ℝ) = ((500000000000 / 964949928469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (329385763 / 500000000) ≤ -Real.log (250000000000 / 483104238259) ∧
    -Real.log (250000000000 / 483104238259) ≤ (658771527 / 1000000000) := by
  have h := checkLog_sound (w := (233104238259 / 733104238259)) (n := 12)
    (lo := (329385763 / 500000000)) (hi := (658771527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((483104238259 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(483104238259 / 250000000000) = 1/(250000000000 / 483104238259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (329385763 / 500000000) (658771527 / 1000000000) (Real.log (483104238259 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (483104238259 / 250000000000) = -Real.log (250000000000 / 483104238259) := by
    rw [show ((483104238259 / 250000000000) : ℝ) = ((250000000000 / 483104238259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (18347539 / 40000000) ≤ -Real.log (250000000000 / 395499448743) ∧
    -Real.log (250000000000 / 395499448743) ≤ (114672119 / 250000000) := by
  have h := checkLog_sound (w := (145499448743 / 645499448743)) (n := 12)
    (lo := (18347539 / 40000000)) (hi := (114672119 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((395499448743 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(395499448743 / 250000000000) = 1/(250000000000 / 395499448743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (18347539 / 40000000) (114672119 / 250000000) (Real.log (395499448743 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (395499448743 / 250000000000) = -Real.log (250000000000 / 395499448743) := by
    rw [show ((395499448743 / 250000000000) : ℝ) = ((250000000000 / 395499448743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (229787817 / 500000000) ≤ -Real.log (500000000000 / 791700950563) ∧
    -Real.log (500000000000 / 791700950563) ≤ (91915127 / 200000000) := by
  have h := checkLog_sound (w := (291700950563 / 1291700950563)) (n := 12)
    (lo := (229787817 / 500000000)) (hi := (91915127 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((791700950563 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(791700950563 / 500000000000) = 1/(500000000000 / 791700950563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (229787817 / 500000000) (91915127 / 200000000) (Real.log (791700950563 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (791700950563 / 500000000000) = -Real.log (500000000000 / 791700950563) := by
    rw [show ((791700950563 / 500000000000) : ℝ) = ((500000000000 / 791700950563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (40773207 / 125000000) ≤ -Real.log (250000000000 / 346418151151) ∧
    -Real.log (250000000000 / 346418151151) ≤ (326185657 / 1000000000) := by
  have h := checkLog_sound (w := (96418151151 / 596418151151)) (n := 12)
    (lo := (40773207 / 125000000)) (hi := (326185657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((346418151151 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(346418151151 / 250000000000) = 1/(250000000000 / 346418151151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (40773207 / 125000000) (326185657 / 1000000000) (Real.log (346418151151 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (346418151151 / 250000000000) = -Real.log (250000000000 / 346418151151) := by
    rw [show ((346418151151 / 250000000000) : ℝ) = ((250000000000 / 346418151151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (326824381 / 1000000000) ≤ -Real.log (500000000000 / 693278975499) ∧
    -Real.log (500000000000 / 693278975499) ≤ (163412191 / 500000000) := by
  have h := checkLog_sound (w := (193278975499 / 1193278975499)) (n := 12)
    (lo := (326824381 / 1000000000)) (hi := (163412191 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((693278975499 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(693278975499 / 500000000000) = 1/(500000000000 / 693278975499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (326824381 / 1000000000) (163412191 / 500000000) (Real.log (693278975499 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (693278975499 / 500000000000) = -Real.log (500000000000 / 693278975499) := by
    rw [show ((693278975499 / 500000000000) : ℝ) = ((500000000000 / 693278975499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (26585537 / 1000000000) ≤ -Real.log (973764747271 / 1000000000000) ∧
    -Real.log (973764747271 / 1000000000000) ≤ (13292769 / 500000000) := by
  have h := checkLog_sound (w := (26235252729 / 1973764747271)) (n := 12)
    (lo := (26585537 / 1000000000)) (hi := (13292769 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 973764747271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 973764747271) = 1/(973764747271 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-13292769 / 500000000) (-26585537 / 1000000000) (Real.log (973764747271 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (1324109 / 50000000) ≤ -Real.log (243466349439 / 250000000000) ∧
    -Real.log (243466349439 / 250000000000) ≤ (26482181 / 1000000000) := by
  have h := checkLog_sound (w := (6533650561 / 493466349439)) (n := 12)
    (lo := (1324109 / 50000000)) (hi := (26482181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243466349439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243466349439) = 1/(243466349439 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-26482181 / 1000000000) (-1324109 / 50000000) (Real.log (243466349439 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell115

end


