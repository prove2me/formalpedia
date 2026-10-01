-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0151Logs__5
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapLowMiddle_Cell0151Logs__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:58:20.755975+00:00
-- url     : https://prove2.me/theorems/effdb0bc-1304-4785-baf3-a7daecb5c71f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0151Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0152Logs, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0151Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0152Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0153Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0154Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0155Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0151Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0152Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0153Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0154Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0155Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0151Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0152Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0153Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0154Logs, GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0155Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0151Logs (+4 modules: GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0152Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0153Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0154Logs, GeneralCK/Certificates/Generated/DoubleCapLowMiddle/Cell0155Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0151Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0151
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

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

theorem reflection_log_1_neg : (652650653 / 1000000000) ≤ -Real.log (1600 / 3073) ∧
    -Real.log (1600 / 3073) ≤ (326325327 / 500000000) := by
  have h := checkLog_sound (w := (1473 / 4673)) (n := 12)
    (lo := (652650653 / 1000000000)) (hi := (326325327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3073 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3073 / 1600) = 1/(1600 / 3073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (652650653 / 1000000000) (326325327 / 500000000) (Real.log (3073 / 1600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3073 / 1600) = -Real.log (1600 / 3073) := by
    rw [show ((3073 / 1600) : ℝ) = ((1600 / 3073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (126678591 / 50000000) ≤ -Real.log (127 / 1600) ∧
    -Real.log (127 / 1600) ≤ (158348239 / 62500000) := by
  have h := checkLog_sound (w := (73 / 327)) (n := 12)
    (lo := (11353257 / 25000000)) (hi := (454130281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 127) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(200 / 127) = 1/(127 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-158348239 / 62500000) (-126678591 / 50000000) (Real.log (127 / 1600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (325938747 / 500000000) ≤ -Real.log (2560 / 4913) ∧
    -Real.log (2560 / 4913) ≤ (130375499 / 200000000) := by
  have h := checkLog_sound (w := (2353 / 7473)) (n := 12)
    (lo := (325938747 / 500000000)) (hi := (130375499 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4913 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4913 / 2560) = 1/(2560 / 4913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (325938747 / 500000000) (130375499 / 200000000) (Real.log (4913 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (4913 / 2560) = -Real.log (2560 / 4913) := by
    rw [show ((4913 / 2560) : ℝ) = ((2560 / 4913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1257521871 / 500000000) ≤ -Real.log (207 / 2560) ∧
    -Real.log (207 / 2560) ≤ (1257521873 / 500000000) := by
  have h := checkLog_sound (w := (113 / 527)) (n := 12)
    (lo := (217801101 / 500000000)) (hi := (435602203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 207) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(320 / 207) = 1/(207 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1257521873 / 500000000) (-1257521871 / 500000000) (Real.log (207 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (38152793 / 62500000) ≤ -Real.log (800 / 1473) ∧
    -Real.log (800 / 1473) ≤ (610444689 / 1000000000) := by
  have h := checkLog_sound (w := (673 / 2273)) (n := 12)
    (lo := (38152793 / 62500000)) (hi := (610444689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1473 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1473 / 800) = 1/(800 / 1473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (38152793 / 62500000) (610444689 / 1000000000) (Real.log (1473 / 800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1473 / 800) = -Real.log (800 / 1473) := by
    rw [show ((1473 / 800) : ℝ) = ((800 / 1473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (5751327 / 3125000) ≤ -Real.log (127 / 800) ∧
    -Real.log (127 / 800) ≤ (1840424643 / 1000000000) := by
  have h := checkLog_sound (w := (73 / 327)) (n := 12)
    (lo := (11353257 / 25000000)) (hi := (454130281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 127) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(200 / 127) = 1/(127 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1840424643 / 1000000000) (-5751327 / 3125000) (Real.log (127 / 800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (608831031 / 1000000000) ≤ -Real.log (1280 / 2353) ∧
    -Real.log (1280 / 2353) ≤ (76103879 / 125000000) := by
  have h := checkLog_sound (w := (1073 / 3633)) (n := 12)
    (lo := (608831031 / 1000000000)) (hi := (76103879 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2353 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2353 / 1280) = 1/(1280 / 2353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (608831031 / 1000000000) (76103879 / 125000000) (Real.log (2353 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2353 / 1280) = -Real.log (1280 / 2353) := by
    rw [show ((2353 / 1280) : ℝ) = ((1280 / 2353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (910948281 / 500000000) ≤ -Real.log (207 / 1280) ∧
    -Real.log (207 / 1280) ≤ (364379313 / 200000000) := by
  have h := checkLog_sound (w := (113 / 527)) (n := 12)
    (lo := (217801101 / 500000000)) (hi := (435602203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 207) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 207) = 1/(207 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-364379313 / 200000000) (-910948281 / 500000000) (Real.log (207 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (660985493 / 1000000000) ≤ -Real.log (10000 / 19367) ∧
    -Real.log (10000 / 19367) ≤ (330492747 / 500000000) := by
  have h := checkLog_sound (w := (9367 / 29367)) (n := 12)
    (lo := (660985493 / 1000000000)) (hi := (330492747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19367 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19367 / 10000) = 1/(10000 / 19367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (660985493 / 1000000000) (330492747 / 500000000) (Real.log (19367 / 10000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (19367 / 10000) = -Real.log (10000 / 19367) := by
    rw [show ((19367 / 10000) : ℝ) = ((10000 / 19367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (689967487 / 250000000) ≤ -Real.log (633 / 10000) ∧
    -Real.log (633 / 10000) ≤ (5390371 / 1953125) := by
  have h := checkLog_sound (w := (617 / 1883)) (n := 12)
    (lo := (85053551 / 125000000)) (hi := (680428409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 633) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1250 / 633) = 1/(633 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-5390371 / 1953125) (-689967487 / 250000000) (Real.log (633 / 10000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (330765559 / 500000000) ≤ -Real.log (1000000 / 1937757) ∧
    -Real.log (1000000 / 1937757) ≤ (661531119 / 1000000000) := by
  have h := checkLog_sound (w := (937757 / 2937757)) (n := 12)
    (lo := (330765559 / 500000000)) (hi := (661531119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1937757 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1937757 / 1000000) = 1/(1000000 / 1937757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (330765559 / 500000000) (661531119 / 1000000000) (Real.log (1937757 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1937757 / 1000000) = -Real.log (1000000 / 1937757) := by
    rw [show ((1937757 / 1000000) : ℝ) = ((1000000 / 1937757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2776709197 / 1000000000) ≤ -Real.log (62243 / 1000000) ∧
    -Real.log (62243 / 1000000) ≤ (1388354601 / 500000000) := by
  have h := checkLog_sound (w := (257 / 124743)) (n := 12)
    (lo := (4120477 / 1000000000)) (hi := (2060239 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 62243) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 62243) = 1/(62243 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1388354601 / 500000000) (-2776709197 / 1000000000) (Real.log (62243 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (6602391 / 10000000) ≤ -Real.log (200000 / 387051) ∧
    -Real.log (200000 / 387051) ≤ (660239101 / 1000000000) := by
  have h := checkLog_sound (w := (187051 / 587051)) (n := 12)
    (lo := (6602391 / 10000000)) (hi := (660239101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((387051 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(387051 / 200000) = 1/(200000 / 387051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (6602391 / 10000000) (660239101 / 1000000000) (Real.log (387051 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (387051 / 200000) = -Real.log (200000 / 387051) := by
    rw [show ((387051 / 200000) : ℝ) = ((200000 / 387051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2737298799 / 1000000000) ≤ -Real.log (12949 / 200000) ∧
    -Real.log (12949 / 200000) ≤ (2737298803 / 1000000000) := by
  have h := checkLog_sound (w := (12051 / 37949)) (n := 12)
    (lo := (657857259 / 1000000000)) (hi := (32892863 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 12949) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(25000 / 12949) = 1/(12949 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2737298803 / 1000000000) (-2737298799 / 1000000000) (Real.log (12949 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (132163327 / 200000000) ≤ -Real.log (1000000 / 1936373) ∧
    -Real.log (1000000 / 1936373) ≤ (165204159 / 250000000) := by
  have h := checkLog_sound (w := (936373 / 2936373)) (n := 12)
    (lo := (132163327 / 200000000)) (hi := (165204159 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1936373 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1936373 / 1000000) = 1/(1000000 / 1936373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (132163327 / 200000000) (165204159 / 250000000) (Real.log (1936373 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1936373 / 1000000) = -Real.log (1000000 / 1936373) := by
    rw [show ((1936373 / 1000000) : ℝ) = ((1000000 / 1936373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (344339671 / 125000000) ≤ -Real.log (63627 / 1000000) ∧
    -Real.log (63627 / 1000000) ≤ (688679343 / 250000000) := by
  have h := checkLog_sound (w := (61373 / 188627)) (n := 12)
    (lo := (168818957 / 250000000)) (hi := (675275829 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 63627) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 63627) = 1/(63627 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-688679343 / 250000000) (-344339671 / 125000000) (Real.log (63627 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3420855441 / 1000000000) ≤ -Real.log (125000000000 / 3824447077409) ∧
    -Real.log (125000000000 / 3824447077409) ≤ (1710427723 / 500000000) := by
  have h := checkLog_sound (w := (1824447077409 / 5824447077409)) (n := 12)
    (lo := (648266721 / 1000000000)) (hi := (324133361 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3824447077409 / 2000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3824447077409 / 2000000000000) = 1/(125000000000 / 3824447077409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3420855441 / 1000000000) (1710427723 / 500000000) (Real.log (3824447077409 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (3824447077409 / 125000000000) = -Real.log (125000000000 / 3824447077409) := by
    rw [show ((3824447077409 / 125000000000) : ℝ) = ((125000000000 / 3824447077409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (859560079 / 250000000) ≤ -Real.log (100000000000 / 3113212730749) ∧
    -Real.log (100000000000 / 3113212730749) ≤ (3438240321 / 1000000000) := by
  have h := checkLog_sound (w := (1513212730749 / 4713212730749)) (n := 12)
    (lo := (166412899 / 250000000)) (hi := (665651597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3113212730749 / 1600000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3113212730749 / 1600000000000) = 1/(100000000000 / 3113212730749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (859560079 / 250000000) (3438240321 / 1000000000) (Real.log (3113212730749 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (3113212730749 / 100000000000) = -Real.log (100000000000 / 3113212730749) := by
    rw [show ((3113212730749 / 100000000000) : ℝ) = ((100000000000 / 3113212730749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3397537899 / 1000000000) ≤ -Real.log (500000000000 / 14945208124179) ∧
    -Real.log (500000000000 / 14945208124179) ≤ (212346119 / 62500000) := by
  have h := checkLog_sound (w := (6945208124179 / 22945208124179)) (n := 12)
    (lo := (624949179 / 1000000000)) (hi := (31247459 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14945208124179 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(14945208124179 / 8000000000000) = 1/(500000000000 / 14945208124179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3397537899 / 1000000000) (212346119 / 62500000) (Real.log (14945208124179 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (14945208124179 / 500000000000) = -Real.log (500000000000 / 14945208124179) := by
    rw [show ((14945208124179 / 500000000000) : ℝ) = ((500000000000 / 14945208124179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3415534003 / 1000000000) ≤ -Real.log (100000000000 / 3043319659893) ∧
    -Real.log (100000000000 / 3043319659893) ≤ (426941751 / 125000000) := by
  have h := checkLog_sound (w := (1443319659893 / 4643319659893)) (n := 12)
    (lo := (642945283 / 1000000000)) (hi := (160736321 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3043319659893 / 1600000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3043319659893 / 1600000000000) = 1/(100000000000 / 3043319659893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3415534003 / 1000000000) (426941751 / 125000000) (Real.log (3043319659893 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (3043319659893 / 100000000000) = -Real.log (100000000000 / 3043319659893) := by
    rw [show ((3043319659893 / 100000000000) : ℝ) = ((100000000000 / 3043319659893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0151

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0152Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0152
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

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

theorem reflection_log_1_neg : (325938747 / 500000000) ≤ -Real.log (2560 / 4913) ∧
    -Real.log (2560 / 4913) ≤ (130375499 / 200000000) := by
  have h := checkLog_sound (w := (2353 / 7473)) (n := 12)
    (lo := (325938747 / 500000000)) (hi := (130375499 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4913 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4913 / 2560) = 1/(2560 / 4913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (325938747 / 500000000) (130375499 / 200000000) (Real.log (4913 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (4913 / 2560) = -Real.log (2560 / 4913) := by
    rw [show ((4913 / 2560) : ℝ) = ((2560 / 4913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1257521871 / 500000000) ≤ -Real.log (207 / 2560) ∧
    -Real.log (207 / 2560) ≤ (1257521873 / 500000000) := by
  have h := checkLog_sound (w := (113 / 527)) (n := 12)
    (lo := (217801101 / 500000000)) (hi := (435602203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 207) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(320 / 207) = 1/(207 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1257521873 / 500000000) (-1257521871 / 500000000) (Real.log (207 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (651103737 / 1000000000) ≤ -Real.log (6400 / 12273) ∧
    -Real.log (6400 / 12273) ≤ (325551869 / 500000000) := by
  have h := checkLog_sound (w := (5873 / 18673)) (n := 12)
    (lo := (651103737 / 1000000000)) (hi := (325551869 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12273 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12273 / 6400) = 1/(6400 / 12273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (651103737 / 1000000000) (325551869 / 500000000) (Real.log (12273 / 6400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12273 / 6400) = -Real.log (6400 / 12273) := by
    rw [show ((12273 / 6400) : ℝ) = ((6400 / 12273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (2496852719 / 1000000000) ≤ -Real.log (527 / 6400) ∧
    -Real.log (527 / 6400) ≤ (2496852723 / 1000000000) := by
  have h := checkLog_sound (w := (273 / 1327)) (n := 12)
    (lo := (417411179 / 1000000000)) (hi := (20870559 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 527) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 527) = 1/(527 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2496852723 / 1000000000) (-2496852719 / 1000000000) (Real.log (527 / 6400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (608831031 / 1000000000) ≤ -Real.log (1280 / 2353) ∧
    -Real.log (1280 / 2353) ≤ (76103879 / 125000000) := by
  have h := checkLog_sound (w := (1073 / 3633)) (n := 12)
    (lo := (608831031 / 1000000000)) (hi := (76103879 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2353 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2353 / 1280) = 1/(1280 / 2353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (608831031 / 1000000000) (76103879 / 125000000) (Real.log (2353 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2353 / 1280) = -Real.log (1280 / 2353) := by
    rw [show ((2353 / 1280) : ℝ) = ((1280 / 2353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (910948281 / 500000000) ≤ -Real.log (207 / 1280) ∧
    -Real.log (207 / 1280) ≤ (364379313 / 200000000) := by
  have h := checkLog_sound (w := (113 / 527)) (n := 12)
    (lo := (217801101 / 500000000)) (hi := (435602203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 207) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 207) = 1/(207 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-364379313 / 200000000) (-910948281 / 500000000) (Real.log (207 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (303607383 / 500000000) ≤ -Real.log (3200 / 5873) ∧
    -Real.log (3200 / 5873) ≤ (607214767 / 1000000000) := by
  have h := checkLog_sound (w := (2673 / 9073)) (n := 12)
    (lo := (303607383 / 500000000)) (hi := (607214767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5873 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5873 / 3200) = 1/(3200 / 5873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (303607383 / 500000000) (607214767 / 1000000000) (Real.log (5873 / 3200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (5873 / 3200) = -Real.log (3200 / 5873) := by
    rw [show ((5873 / 3200) : ℝ) = ((3200 / 5873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1803705539 / 1000000000) ≤ -Real.log (527 / 3200) ∧
    -Real.log (527 / 3200) ≤ (901852771 / 500000000) := by
  have h := checkLog_sound (w := (273 / 1327)) (n := 12)
    (lo := (417411179 / 1000000000)) (hi := (20870559 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 527) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 527) = 1/(527 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-901852771 / 500000000) (-1803705539 / 1000000000) (Real.log (527 / 3200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (660441637 / 1000000000) ≤ -Real.log (1000000 / 1935647) ∧
    -Real.log (1000000 / 1935647) ≤ (330220819 / 500000000) := by
  have h := checkLog_sound (w := (935647 / 2935647)) (n := 12)
    (lo := (660441637 / 1000000000)) (hi := (330220819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1935647 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1935647 / 1000000) = 1/(1000000 / 1935647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (660441637 / 1000000000) (330220819 / 500000000) (Real.log (1935647 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1935647 / 1000000) = -Real.log (1000000 / 1935647) := by
    rw [show ((1935647 / 1000000) : ℝ) = ((1000000 / 1935647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (685842931 / 250000000) ≤ -Real.log (64353 / 1000000) ∧
    -Real.log (64353 / 1000000) ≤ (171460733 / 62500000) := by
  have h := checkLog_sound (w := (60647 / 189353)) (n := 12)
    (lo := (82991273 / 125000000)) (hi := (132786037 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 64353) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 64353) = 1/(64353 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-171460733 / 62500000) (-685842931 / 250000000) (Real.log (64353 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (66098601 / 100000000) ≤ -Real.log (1000000 / 1936701) ∧
    -Real.log (1000000 / 1936701) ≤ (660986011 / 1000000000) := by
  have h := checkLog_sound (w := (936701 / 2936701)) (n := 12)
    (lo := (66098601 / 100000000)) (hi := (660986011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1936701 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1936701 / 1000000) = 1/(1000000 / 1936701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (66098601 / 100000000) (660986011 / 1000000000) (Real.log (1936701 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1936701 / 1000000) = -Real.log (1000000 / 1936701) := by
    rw [show ((1936701 / 1000000) : ℝ) = ((1000000 / 1936701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1379942873 / 500000000) ≤ -Real.log (63299 / 1000000) ∧
    -Real.log (63299 / 1000000) ≤ (11039543 / 4000000) := by
  have h := checkLog_sound (w := (61701 / 188299)) (n := 12)
    (lo := (340222103 / 500000000)) (hi := (680444207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 63299) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 63299) = 1/(63299 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-11039543 / 4000000) (-1379942873 / 500000000) (Real.log (63299 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (659662783 / 1000000000) ≤ -Real.log (50000 / 96707) ∧
    -Real.log (50000 / 96707) ≤ (10307231 / 15625000) := by
  have h := checkLog_sound (w := (46707 / 146707)) (n := 12)
    (lo := (659662783 / 1000000000)) (hi := (10307231 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((96707 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(96707 / 50000) = 1/(50000 / 96707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (659662783 / 1000000000) (10307231 / 15625000) (Real.log (96707 / 50000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (96707 / 50000) = -Real.log (50000 / 96707) := by
    rw [show ((96707 / 50000) : ℝ) = ((50000 / 96707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (85007 / 31250) ≤ -Real.log (3293 / 50000) ∧
    -Real.log (3293 / 50000) ≤ (680056001 / 250000000) := by
  have h := checkLog_sound (w := (2957 / 9543)) (n := 12)
    (lo := (32039123 / 50000000)) (hi := (640782461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 3293) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6250 / 3293) = 1/(3293 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-680056001 / 250000000) (-85007 / 31250) (Real.log (3293 / 50000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (660239617 / 1000000000) ≤ -Real.log (125000 / 241907) ∧
    -Real.log (125000 / 241907) ≤ (330119809 / 500000000) := by
  have h := checkLog_sound (w := (116907 / 366907)) (n := 12)
    (lo := (660239617 / 1000000000)) (hi := (330119809 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((241907 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(241907 / 125000) = 1/(125000 / 241907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (660239617 / 1000000000) (330119809 / 500000000) (Real.log (241907 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (241907 / 125000) = -Real.log (125000 / 241907) := by
    rw [show ((241907 / 125000) : ℝ) = ((125000 / 241907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (547462849 / 200000000) ≤ -Real.log (8093 / 125000) ∧
    -Real.log (8093 / 125000) ≤ (2737314249 / 1000000000) := by
  have h := checkLog_sound (w := (3766 / 11859)) (n := 12)
    (lo := (131574541 / 200000000)) (hi := (328936353 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8093) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(15625 / 8093) = 1/(8093 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2737314249 / 1000000000) (-547462849 / 200000000) (Real.log (8093 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3403813361 / 1000000000) ≤ -Real.log (25000000000 / 751964554877) ∧
    -Real.log (25000000000 / 751964554877) ≤ (1701906683 / 500000000) := by
  have h := checkLog_sound (w := (351964554877 / 1151964554877)) (n := 12)
    (lo := (631224641 / 1000000000)) (hi := (315612321 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((751964554877 / 400000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(751964554877 / 400000000000) = 1/(25000000000 / 751964554877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3403813361 / 1000000000) (1701906683 / 500000000) (Real.log (751964554877 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (751964554877 / 25000000000) = -Real.log (25000000000 / 751964554877) := by
    rw [show ((751964554877 / 25000000000) : ℝ) = ((25000000000 / 751964554877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (684174351 / 200000000) ≤ -Real.log (100000000000 / 3059607576739) ∧
    -Real.log (100000000000 / 3059607576739) ≤ (42760897 / 12500000) := by
  have h := checkLog_sound (w := (1459607576739 / 4659607576739)) (n := 12)
    (lo := (129656607 / 200000000)) (hi := (162070759 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3059607576739 / 1600000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3059607576739 / 1600000000000) = 1/(100000000000 / 3059607576739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (684174351 / 200000000) (42760897 / 12500000) (Real.log (3059607576739 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (3059607576739 / 100000000000) = -Real.log (100000000000 / 3059607576739) := by
    rw [show ((3059607576739 / 100000000000) : ℝ) = ((100000000000 / 3059607576739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3379886783 / 1000000000) ≤ -Real.log (500000000000 / 14683723048891) ∧
    -Real.log (500000000000 / 14683723048891) ≤ (844971697 / 250000000) := by
  have h := checkLog_sound (w := (6683723048891 / 22683723048891)) (n := 12)
    (lo := (607298063 / 1000000000)) (hi := (37956129 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14683723048891 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(14683723048891 / 8000000000000) = 1/(500000000000 / 14683723048891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3379886783 / 1000000000) (844971697 / 250000000) (Real.log (14683723048891 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (14683723048891 / 500000000000) = -Real.log (500000000000 / 14683723048891) := by
    rw [show ((14683723048891 / 500000000000) : ℝ) = ((500000000000 / 14683723048891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1698776931 / 500000000) ≤ -Real.log (500000000000 / 14945446682319) ∧
    -Real.log (500000000000 / 14945446682319) ≤ (3397553867 / 1000000000) := by
  have h := checkLog_sound (w := (6945446682319 / 22945446682319)) (n := 12)
    (lo := (312482571 / 500000000)) (hi := (624965143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14945446682319 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(14945446682319 / 8000000000000) = 1/(500000000000 / 14945446682319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1698776931 / 500000000) (3397553867 / 1000000000) (Real.log (14945446682319 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (14945446682319 / 500000000000) = -Real.log (500000000000 / 14945446682319) := by
    rw [show ((14945446682319 / 500000000000) : ℝ) = ((500000000000 / 14945446682319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0152

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0153Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0153
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

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

theorem reflection_log_1_neg : (651103737 / 1000000000) ≤ -Real.log (6400 / 12273) ∧
    -Real.log (6400 / 12273) ≤ (325551869 / 500000000) := by
  have h := checkLog_sound (w := (5873 / 18673)) (n := 12)
    (lo := (651103737 / 1000000000)) (hi := (325551869 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12273 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12273 / 6400) = 1/(6400 / 12273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (651103737 / 1000000000) (325551869 / 500000000) (Real.log (12273 / 6400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12273 / 6400) = -Real.log (6400 / 12273) := by
    rw [show ((12273 / 6400) : ℝ) = ((6400 / 12273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (2496852719 / 1000000000) ≤ -Real.log (527 / 6400) ∧
    -Real.log (527 / 6400) ≤ (2496852723 / 1000000000) := by
  have h := checkLog_sound (w := (273 / 1327)) (n := 12)
    (lo := (417411179 / 1000000000)) (hi := (20870559 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 527) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 527) = 1/(527 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2496852723 / 1000000000) (-2496852719 / 1000000000) (Real.log (527 / 6400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (32516469 / 50000000) ≤ -Real.log (12800 / 24527) ∧
    -Real.log (12800 / 24527) ≤ (650329381 / 1000000000) := by
  have h := checkLog_sound (w := (11727 / 37327)) (n := 12)
    (lo := (32516469 / 50000000)) (hi := (650329381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24527 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24527 / 12800) = 1/(12800 / 24527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (32516469 / 50000000) (650329381 / 1000000000) (Real.log (24527 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24527 / 12800) = -Real.log (12800 / 24527) := by
    rw [show ((24527 / 12800) : ℝ) = ((12800 / 24527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (495797341 / 200000000) ≤ -Real.log (1073 / 12800) ∧
    -Real.log (1073 / 12800) ≤ (2478986709 / 1000000000) := by
  have h := checkLog_sound (w := (527 / 2673)) (n := 12)
    (lo := (79909033 / 200000000)) (hi := (199772583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1073) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1073) = 1/(1073 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2478986709 / 1000000000) (-495797341 / 200000000) (Real.log (1073 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (303607383 / 500000000) ≤ -Real.log (3200 / 5873) ∧
    -Real.log (3200 / 5873) ≤ (607214767 / 1000000000) := by
  have h := checkLog_sound (w := (2673 / 9073)) (n := 12)
    (lo := (303607383 / 500000000)) (hi := (607214767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5873 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5873 / 3200) = 1/(3200 / 5873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (303607383 / 500000000) (607214767 / 1000000000) (Real.log (5873 / 3200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (5873 / 3200) = -Real.log (3200 / 5873) := by
    rw [show ((5873 / 3200) : ℝ) = ((3200 / 5873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1803705539 / 1000000000) ≤ -Real.log (527 / 3200) ∧
    -Real.log (527 / 3200) ≤ (901852771 / 500000000) := by
  have h := checkLog_sound (w := (273 / 1327)) (n := 12)
    (lo := (417411179 / 1000000000)) (hi := (20870559 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 527) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 527) = 1/(527 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-901852771 / 500000000) (-1803705539 / 1000000000) (Real.log (527 / 3200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (121119177 / 200000000) ≤ -Real.log (6400 / 11727) ∧
    -Real.log (6400 / 11727) ≤ (302797943 / 500000000) := by
  have h := checkLog_sound (w := (5327 / 18127)) (n := 12)
    (lo := (121119177 / 200000000)) (hi := (302797943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11727 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11727 / 6400) = 1/(6400 / 11727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (121119177 / 200000000) (302797943 / 500000000) (Real.log (11727 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (11727 / 6400) = -Real.log (6400 / 11727) := by
    rw [show ((11727 / 6400) : ℝ) = ((6400 / 11727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (71433581 / 40000000) ≤ -Real.log (1073 / 6400) ∧
    -Real.log (1073 / 6400) ≤ (223229941 / 125000000) := by
  have h := checkLog_sound (w := (527 / 2673)) (n := 12)
    (lo := (79909033 / 200000000)) (hi := (199772583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1073) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1073) = 1/(1073 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-223229941 / 125000000) (-71433581 / 40000000) (Real.log (1073 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (164974759 / 250000000) ≤ -Real.log (1000000 / 1934597) ∧
    -Real.log (1000000 / 1934597) ≤ (659899037 / 1000000000) := by
  have h := checkLog_sound (w := (934597 / 2934597)) (n := 12)
    (lo := (164974759 / 250000000)) (hi := (659899037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1934597 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1934597 / 1000000) = 1/(1000000 / 1934597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (164974759 / 250000000) (659899037 / 1000000000) (Real.log (1934597 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1934597 / 1000000) = -Real.log (1000000 / 1934597) := by
    rw [show ((1934597 / 1000000) : ℝ) = ((1000000 / 1934597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (681796787 / 250000000) ≤ -Real.log (65403 / 1000000) ∧
    -Real.log (65403 / 1000000) ≤ (170449197 / 62500000) := by
  have h := checkLog_sound (w := (59597 / 190403)) (n := 12)
    (lo := (80968201 / 125000000)) (hi := (647745609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 65403) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 65403) = 1/(65403 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-170449197 / 62500000) (-681796787 / 250000000) (Real.log (65403 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (330221077 / 500000000) ≤ -Real.log (31250 / 60489) ∧
    -Real.log (31250 / 60489) ≤ (132088431 / 200000000) := by
  have h := checkLog_sound (w := (29239 / 91739)) (n := 12)
    (lo := (330221077 / 500000000)) (hi := (132088431 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60489 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60489 / 31250) = 1/(31250 / 60489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (330221077 / 500000000) (132088431 / 200000000) (Real.log (60489 / 31250)) := by
  have h := reflection_log_11_neg
  have he : Real.log (60489 / 31250) = -Real.log (31250 / 60489) := by
    rw [show ((60489 / 31250) : ℝ) = ((31250 / 60489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2743387263 / 1000000000) ≤ -Real.log (2011 / 31250) ∧
    -Real.log (2011 / 31250) ≤ (2743387267 / 1000000000) := by
  have h := checkLog_sound (w := (7581 / 23669)) (n := 12)
    (lo := (663945723 / 1000000000)) (hi := (165986431 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8044) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(15625 / 8044) = 1/(2011 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2743387267 / 1000000000) (-2743387263 / 1000000000) (Real.log (2011 / 31250)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (10298237 / 15625000) ≤ -Real.log (1000000 / 1933027) ∧
    -Real.log (1000000 / 1933027) ≤ (659087169 / 1000000000) := by
  have h := checkLog_sound (w := (933027 / 2933027)) (n := 12)
    (lo := (10298237 / 15625000)) (hi := (659087169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1933027 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1933027 / 1000000) = 1/(1000000 / 1933027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (10298237 / 15625000) (659087169 / 1000000000) (Real.log (1933027 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1933027 / 1000000) = -Real.log (1000000 / 1933027) := by
    rw [show ((1933027 / 1000000) : ℝ) = ((1000000 / 1933027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (675866431 / 250000000) ≤ -Real.log (66973 / 1000000) ∧
    -Real.log (66973 / 1000000) ≤ (10560413 / 3906250) := by
  have h := checkLog_sound (w := (58027 / 191973)) (n := 12)
    (lo := (78003023 / 125000000)) (hi := (124804837 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 66973) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 66973) = 1/(66973 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-10560413 / 3906250) (-675866431 / 250000000) (Real.log (66973 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (6596633 / 10000000) ≤ -Real.log (1000000 / 1934141) ∧
    -Real.log (1000000 / 1934141) ≤ (659663301 / 1000000000) := by
  have h := checkLog_sound (w := (934141 / 2934141)) (n := 12)
    (lo := (6596633 / 10000000)) (hi := (659663301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1934141 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1934141 / 1000000) = 1/(1000000 / 1934141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (6596633 / 10000000) (659663301 / 1000000000) (Real.log (1934141 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1934141 / 1000000) = -Real.log (1000000 / 1934141) := by
    rw [show ((1934141 / 1000000) : ℝ) = ((1000000 / 1934141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (170014949 / 62500000) ≤ -Real.log (65859 / 1000000) ∧
    -Real.log (65859 / 1000000) ≤ (680059797 / 250000000) := by
  have h := checkLog_sound (w := (59141 / 190859)) (n := 12)
    (lo := (160199411 / 250000000)) (hi := (128159529 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 65859) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 65859) = 1/(65859 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-680059797 / 250000000) (-170014949 / 62500000) (Real.log (65859 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3387086183 / 1000000000) ≤ -Real.log (250000000000 / 7394909254927) ∧
    -Real.log (250000000000 / 7394909254927) ≤ (846771547 / 250000000) := by
  have h := checkLog_sound (w := (3394909254927 / 11394909254927)) (n := 12)
    (lo := (614497463 / 1000000000)) (hi := (76812183 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7394909254927 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(7394909254927 / 4000000000000) = 1/(250000000000 / 7394909254927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3387086183 / 1000000000) (846771547 / 250000000) (Real.log (7394909254927 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (7394909254927 / 250000000000) = -Real.log (250000000000 / 7394909254927) := by
    rw [show ((7394909254927 / 250000000000) : ℝ) = ((250000000000 / 7394909254927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3403829417 / 1000000000) ≤ -Real.log (500000000000 / 15039532570861) ∧
    -Real.log (500000000000 / 15039532570861) ≤ (1701914711 / 500000000) := by
  have h := checkLog_sound (w := (7039532570861 / 23039532570861)) (n := 12)
    (lo := (631240697 / 1000000000)) (hi := (315620349 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15039532570861 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15039532570861 / 8000000000000) = 1/(500000000000 / 15039532570861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3403829417 / 1000000000) (1701914711 / 500000000) (Real.log (15039532570861 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (15039532570861 / 500000000000) = -Real.log (500000000000 / 15039532570861) := by
    rw [show ((15039532570861 / 500000000000) : ℝ) = ((500000000000 / 15039532570861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3362552891 / 1000000000) ≤ -Real.log (500000000000 / 14431390261747) ∧
    -Real.log (500000000000 / 14431390261747) ≤ (52539889 / 15625000) := by
  have h := checkLog_sound (w := (6431390261747 / 22431390261747)) (n := 12)
    (lo := (589964171 / 1000000000)) (hi := (147491043 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14431390261747 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(14431390261747 / 8000000000000) = 1/(500000000000 / 14431390261747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3362552891 / 1000000000) (52539889 / 15625000) (Real.log (14431390261747 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (14431390261747 / 500000000000) = -Real.log (500000000000 / 14431390261747) := by
    rw [show ((14431390261747 / 500000000000) : ℝ) = ((500000000000 / 14431390261747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3379902483 / 1000000000) ≤ -Real.log (250000000000 / 7341976798919) ∧
    -Real.log (250000000000 / 7341976798919) ≤ (422487811 / 125000000) := by
  have h := checkLog_sound (w := (3341976798919 / 11341976798919)) (n := 12)
    (lo := (607313763 / 1000000000)) (hi := (151828441 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7341976798919 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(7341976798919 / 4000000000000) = 1/(250000000000 / 7341976798919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3379902483 / 1000000000) (422487811 / 125000000) (Real.log (7341976798919 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (7341976798919 / 250000000000) = -Real.log (250000000000 / 7341976798919) := by
    rw [show ((7341976798919 / 250000000000) : ℝ) = ((250000000000 / 7341976798919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0153

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0154Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0154
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

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

theorem reflection_log_1_neg : (32516469 / 50000000) ≤ -Real.log (12800 / 24527) ∧
    -Real.log (12800 / 24527) ≤ (650329381 / 1000000000) := by
  have h := checkLog_sound (w := (11727 / 37327)) (n := 12)
    (lo := (32516469 / 50000000)) (hi := (650329381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24527 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24527 / 12800) = 1/(12800 / 24527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (32516469 / 50000000) (650329381 / 1000000000) (Real.log (24527 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24527 / 12800) = -Real.log (12800 / 24527) := by
    rw [show ((24527 / 12800) : ℝ) = ((12800 / 24527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (495797341 / 200000000) ≤ -Real.log (1073 / 12800) ∧
    -Real.log (1073 / 12800) ≤ (2478986709 / 1000000000) := by
  have h := checkLog_sound (w := (527 / 2673)) (n := 12)
    (lo := (79909033 / 200000000)) (hi := (199772583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1073) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1073) = 1/(1073 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2478986709 / 1000000000) (-495797341 / 200000000) (Real.log (1073 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (649554423 / 1000000000) ≤ -Real.log (3200 / 6127) ∧
    -Real.log (3200 / 6127) ≤ (81194303 / 125000000) := by
  have h := checkLog_sound (w := (2927 / 9327)) (n := 12)
    (lo := (649554423 / 1000000000)) (hi := (81194303 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6127 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6127 / 3200) = 1/(3200 / 6127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (649554423 / 1000000000) (81194303 / 125000000) (Real.log (6127 / 3200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6127 / 3200) = -Real.log (3200 / 6127) := by
    rw [show ((6127 / 3200) : ℝ) = ((3200 / 6127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (2461434291 / 1000000000) ≤ -Real.log (273 / 3200) ∧
    -Real.log (273 / 3200) ≤ (492286859 / 200000000) := by
  have h := checkLog_sound (w := (127 / 673)) (n := 12)
    (lo := (381992751 / 1000000000)) (hi := (23874547 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 273) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(400 / 273) = 1/(273 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-492286859 / 200000000) (-2461434291 / 1000000000) (Real.log (273 / 3200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (121119177 / 200000000) ≤ -Real.log (6400 / 11727) ∧
    -Real.log (6400 / 11727) ≤ (302797943 / 500000000) := by
  have h := checkLog_sound (w := (5327 / 18127)) (n := 12)
    (lo := (121119177 / 200000000)) (hi := (302797943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11727 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11727 / 6400) = 1/(6400 / 11727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (121119177 / 200000000) (302797943 / 500000000) (Real.log (11727 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (11727 / 6400) = -Real.log (6400 / 11727) := by
    rw [show ((11727 / 6400) : ℝ) = ((6400 / 11727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (71433581 / 40000000) ≤ -Real.log (1073 / 6400) ∧
    -Real.log (1073 / 6400) ≤ (223229941 / 125000000) := by
  have h := checkLog_sound (w := (527 / 2673)) (n := 12)
    (lo := (79909033 / 200000000)) (hi := (199772583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1073) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1073) = 1/(1073 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-223229941 / 125000000) (-71433581 / 40000000) (Real.log (1073 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (301987189 / 500000000) ≤ -Real.log (1600 / 2927) ∧
    -Real.log (1600 / 2927) ≤ (603974379 / 1000000000) := by
  have h := checkLog_sound (w := (1327 / 4527)) (n := 12)
    (lo := (301987189 / 500000000)) (hi := (603974379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2927 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2927 / 1600) = 1/(1600 / 2927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (301987189 / 500000000) (603974379 / 1000000000) (Real.log (2927 / 1600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2927 / 1600) = -Real.log (1600 / 2927) := by
    rw [show ((2927 / 1600) : ℝ) = ((1600 / 2927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1768287111 / 1000000000) ≤ -Real.log (273 / 1600) ∧
    -Real.log (273 / 1600) ≤ (884143557 / 500000000) := by
  have h := checkLog_sound (w := (127 / 673)) (n := 12)
    (lo := (381992751 / 1000000000)) (hi := (23874547 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 273) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(400 / 273) = 1/(273 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-884143557 / 500000000) (-1768287111 / 1000000000) (Real.log (273 / 1600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (659357691 / 1000000000) ≤ -Real.log (20000 / 38671) ∧
    -Real.log (20000 / 38671) ≤ (164839423 / 250000000) := by
  have h := checkLog_sound (w := (18671 / 58671)) (n := 12)
    (lo := (659357691 / 1000000000)) (hi := (164839423 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38671 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38671 / 20000) = 1/(20000 / 38671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (659357691 / 1000000000) (164839423 / 250000000) (Real.log (38671 / 20000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (38671 / 20000) = -Real.log (20000 / 38671) := by
    rw [show ((38671 / 20000) : ℝ) = ((20000 / 38671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (677826373 / 250000000) ≤ -Real.log (1329 / 20000) ∧
    -Real.log (1329 / 20000) ≤ (338913187 / 125000000) := by
  have h := checkLog_sound (w := (1171 / 3829)) (n := 12)
    (lo := (39491497 / 62500000)) (hi := (631863953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 1329) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2500 / 1329) = 1/(1329 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-338913187 / 125000000) (-677826373 / 250000000) (Real.log (1329 / 20000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (20621861 / 31250000) ≤ -Real.log (500000 / 967299) ∧
    -Real.log (500000 / 967299) ≤ (659899553 / 1000000000) := by
  have h := checkLog_sound (w := (467299 / 1467299)) (n := 12)
    (lo := (20621861 / 31250000)) (hi := (659899553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((967299 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(967299 / 500000) = 1/(500000 / 967299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (20621861 / 31250000) (659899553 / 1000000000) (Real.log (967299 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (967299 / 500000) = -Real.log (500000 / 967299) := by
    rw [show ((967299 / 500000) : ℝ) = ((500000 / 967299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1363601219 / 500000000) ≤ -Real.log (32701 / 500000) ∧
    -Real.log (32701 / 500000) ≤ (1363601221 / 500000000) := by
  have h := checkLog_sound (w := (29799 / 95201)) (n := 12)
    (lo := (323880449 / 500000000)) (hi := (647760899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 32701) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 32701) = 1/(32701 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1363601221 / 500000000) (-1363601219 / 500000000) (Real.log (32701 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (329255869 / 500000000) ≤ -Real.log (200000 / 386383) ∧
    -Real.log (200000 / 386383) ≤ (658511739 / 1000000000) := by
  have h := checkLog_sound (w := (186383 / 586383)) (n := 12)
    (lo := (329255869 / 500000000)) (hi := (658511739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((386383 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(386383 / 200000) = 1/(200000 / 386383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (329255869 / 500000000) (658511739 / 1000000000) (Real.log (386383 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (386383 / 200000) = -Real.log (200000 / 386383) := by
    rw [show ((386383 / 200000) : ℝ) = ((200000 / 386383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (167937397 / 62500000) ≤ -Real.log (13617 / 200000) ∧
    -Real.log (13617 / 200000) ≤ (671749589 / 250000000) := by
  have h := checkLog_sound (w := (11383 / 38617)) (n := 12)
    (lo := (151889203 / 250000000)) (hi := (607556813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 13617) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(25000 / 13617) = 1/(13617 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-671749589 / 250000000) (-167937397 / 62500000) (Real.log (13617 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (131817537 / 200000000) ≤ -Real.log (250000 / 483257) ∧
    -Real.log (250000 / 483257) ≤ (329543843 / 500000000) := by
  have h := checkLog_sound (w := (233257 / 733257)) (n := 12)
    (lo := (131817537 / 200000000)) (hi := (329543843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((483257 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(483257 / 250000) = 1/(250000 / 483257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (131817537 / 200000000) (329543843 / 500000000) (Real.log (483257 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (483257 / 250000) = -Real.log (250000 / 483257) := by
    rw [show ((483257 / 250000) : ℝ) = ((250000 / 483257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (540696131 / 200000000) ≤ -Real.log (16743 / 250000) ∧
    -Real.log (16743 / 250000) ≤ (2703480659 / 1000000000) := by
  have h := checkLog_sound (w := (14507 / 47993)) (n := 12)
    (lo := (124807823 / 200000000)) (hi := (156009779 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 16743) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(31250 / 16743) = 1/(16743 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2703480659 / 1000000000) (-540696131 / 200000000) (Real.log (16743 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3370663183 / 1000000000) ≤ -Real.log (5000000000 / 145489089541) ∧
    -Real.log (5000000000 / 145489089541) ≤ (842665797 / 250000000) := by
  have h := checkLog_sound (w := (65489089541 / 225489089541)) (n := 12)
    (lo := (598074463 / 1000000000)) (hi := (18689827 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145489089541 / 80000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(145489089541 / 80000000000) = 1/(5000000000 / 145489089541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3370663183 / 1000000000) (842665797 / 250000000) (Real.log (145489089541 / 5000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (145489089541 / 5000000000) = -Real.log (5000000000 / 145489089541) := by
    rw [show ((145489089541 / 5000000000) : ℝ) = ((5000000000 / 145489089541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (338710199 / 100000000) ≤ -Real.log (500000000000 / 14790052291979) ∧
    -Real.log (500000000000 / 14790052291979) ≤ (677420399 / 200000000) := by
  have h := checkLog_sound (w := (6790052291979 / 22790052291979)) (n := 12)
    (lo := (61451327 / 100000000)) (hi := (614513271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14790052291979 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(14790052291979 / 8000000000000) = 1/(500000000000 / 14790052291979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (338710199 / 100000000) (677420399 / 200000000) (Real.log (14790052291979 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (14790052291979 / 500000000000) = -Real.log (500000000000 / 14790052291979) := by
    rw [show ((14790052291979 / 500000000000) : ℝ) = ((500000000000 / 14790052291979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3345510091 / 1000000000) ≤ -Real.log (250000000000 / 7093761474627) ∧
    -Real.log (250000000000 / 7093761474627) ≤ (209094381 / 62500000) := by
  have h := checkLog_sound (w := (3093761474627 / 11093761474627)) (n := 12)
    (lo := (572921371 / 1000000000)) (hi := (143230343 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7093761474627 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(7093761474627 / 4000000000000) = 1/(250000000000 / 7093761474627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3345510091 / 1000000000) (209094381 / 62500000) (Real.log (7093761474627 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (7093761474627 / 250000000000) = -Real.log (250000000000 / 7093761474627) := by
    rw [show ((7093761474627 / 250000000000) : ℝ) = ((250000000000 / 7093761474627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (168128417 / 50000000) ≤ -Real.log (125000000000 / 3607903302873) ∧
    -Real.log (125000000000 / 3607903302873) ≤ (672513669 / 200000000) := by
  have h := checkLog_sound (w := (1607903302873 / 5607903302873)) (n := 12)
    (lo := (29498981 / 50000000)) (hi := (589979621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3607903302873 / 2000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3607903302873 / 2000000000000) = 1/(125000000000 / 3607903302873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (168128417 / 50000000) (672513669 / 200000000) (Real.log (3607903302873 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (3607903302873 / 125000000000) = -Real.log (125000000000 / 3607903302873) := by
    rw [show ((3607903302873 / 125000000000) : ℝ) = ((125000000000 / 3607903302873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0154

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0155Logs =====
section
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0155
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

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

theorem reflection_log_1_neg : (649554423 / 1000000000) ≤ -Real.log (3200 / 6127) ∧
    -Real.log (3200 / 6127) ≤ (81194303 / 125000000) := by
  have h := checkLog_sound (w := (2927 / 9327)) (n := 12)
    (lo := (649554423 / 1000000000)) (hi := (81194303 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6127 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6127 / 3200) = 1/(3200 / 6127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (649554423 / 1000000000) (81194303 / 125000000) (Real.log (6127 / 3200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6127 / 3200) = -Real.log (3200 / 6127) := by
    rw [show ((6127 / 3200) : ℝ) = ((3200 / 6127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (2461434291 / 1000000000) ≤ -Real.log (273 / 3200) ∧
    -Real.log (273 / 3200) ≤ (492286859 / 200000000) := by
  have h := checkLog_sound (w := (127 / 673)) (n := 12)
    (lo := (381992751 / 1000000000)) (hi := (23874547 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 273) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(400 / 273) = 1/(273 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-492286859 / 200000000) (-2461434291 / 1000000000) (Real.log (273 / 3200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (324389433 / 500000000) ≤ -Real.log (12800 / 24489) ∧
    -Real.log (12800 / 24489) ≤ (648778867 / 1000000000) := by
  have h := checkLog_sound (w := (11689 / 37289)) (n := 12)
    (lo := (324389433 / 500000000)) (hi := (648778867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24489 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24489 / 12800) = 1/(12800 / 24489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (324389433 / 500000000) (648778867 / 1000000000) (Real.log (24489 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24489 / 12800) = -Real.log (12800 / 24489) := by
    rw [show ((24489 / 12800) : ℝ) = ((12800 / 24489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1222092329 / 500000000) ≤ -Real.log (1111 / 12800) ∧
    -Real.log (1111 / 12800) ≤ (1222092331 / 500000000) := by
  have h := checkLog_sound (w := (489 / 2711)) (n := 12)
    (lo := (182371559 / 500000000)) (hi := (364743119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1111) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1111) = 1/(1111 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1222092331 / 500000000) (-1222092329 / 500000000) (Real.log (1111 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (301987189 / 500000000) ≤ -Real.log (1600 / 2927) ∧
    -Real.log (1600 / 2927) ≤ (603974379 / 1000000000) := by
  have h := checkLog_sound (w := (1327 / 4527)) (n := 12)
    (lo := (301987189 / 500000000)) (hi := (603974379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2927 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2927 / 1600) = 1/(1600 / 2927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (301987189 / 500000000) (603974379 / 1000000000) (Real.log (2927 / 1600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2927 / 1600) = -Real.log (1600 / 2927) := by
    rw [show ((2927 / 1600) : ℝ) = ((1600 / 2927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1768287111 / 1000000000) ≤ -Real.log (273 / 1600) ∧
    -Real.log (273 / 1600) ≤ (884143557 / 500000000) := by
  have h := checkLog_sound (w := (127 / 673)) (n := 12)
    (lo := (381992751 / 1000000000)) (hi := (23874547 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 273) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(400 / 273) = 1/(273 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-884143557 / 500000000) (-1768287111 / 1000000000) (Real.log (273 / 1600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (301175119 / 500000000) ≤ -Real.log (6400 / 11689) ∧
    -Real.log (6400 / 11689) ≤ (602350239 / 1000000000) := by
  have h := checkLog_sound (w := (5289 / 18089)) (n := 12)
    (lo := (301175119 / 500000000)) (hi := (602350239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11689 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11689 / 6400) = 1/(6400 / 11689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (301175119 / 500000000) (602350239 / 1000000000) (Real.log (11689 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (11689 / 6400) = -Real.log (6400 / 11689) := by
    rw [show ((11689 / 6400) : ℝ) = ((6400 / 11689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (875518739 / 500000000) ≤ -Real.log (1111 / 6400) ∧
    -Real.log (1111 / 6400) ≤ (1751037481 / 1000000000) := by
  have h := checkLog_sound (w := (489 / 2711)) (n := 12)
    (lo := (182371559 / 500000000)) (hi := (364743119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1111) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1111) = 1/(1111 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1751037481 / 1000000000) (-875518739 / 500000000) (Real.log (1111 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (658818123 / 1000000000) ≤ -Real.log (1000000 / 1932507) ∧
    -Real.log (1000000 / 1932507) ≤ (164704531 / 250000000) := by
  have h := checkLog_sound (w := (932507 / 2932507)) (n := 12)
    (lo := (658818123 / 1000000000)) (hi := (164704531 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1932507 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1932507 / 1000000) = 1/(1000000 / 1932507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (658818123 / 1000000000) (164704531 / 250000000) (Real.log (1932507 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1932507 / 1000000) = -Real.log (1000000 / 1932507) := by
    rw [show ((1932507 / 1000000) : ℝ) = ((1000000 / 1932507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (673932847 / 250000000) ≤ -Real.log (67493 / 1000000) ∧
    -Real.log (67493 / 1000000) ≤ (42120803 / 15625000) := by
  have h := checkLog_sound (w := (57507 / 192493)) (n := 12)
    (lo := (77036231 / 125000000)) (hi := (616289849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 67493) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 67493) = 1/(67493 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-42120803 / 15625000) (-673932847 / 250000000) (Real.log (67493 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (1287809 / 1953125) ≤ -Real.log (1000000 / 1933551) ∧
    -Real.log (1000000 / 1933551) ≤ (659358209 / 1000000000) := by
  have h := checkLog_sound (w := (933551 / 2933551)) (n := 12)
    (lo := (1287809 / 1953125)) (hi := (659358209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1933551 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1933551 / 1000000) = 1/(1000000 / 1933551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (1287809 / 1953125) (659358209 / 1000000000) (Real.log (1933551 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1933551 / 1000000) = -Real.log (1000000 / 1933551) := by
    rw [show ((1933551 / 1000000) : ℝ) = ((1000000 / 1933551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2711320541 / 1000000000) ≤ -Real.log (66449 / 1000000) ∧
    -Real.log (66449 / 1000000) ≤ (542264109 / 200000000) := by
  have h := checkLog_sound (w := (58551 / 191449)) (n := 12)
    (lo := (631879001 / 1000000000)) (hi := (315939501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 66449) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 66449) = 1/(66449 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-542264109 / 200000000) (-2711320541 / 1000000000) (Real.log (66449 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (328968507 / 500000000) ≤ -Real.log (200000 / 386161) ∧
    -Real.log (200000 / 386161) ≤ (131587403 / 200000000) := by
  have h := checkLog_sound (w := (186161 / 586161)) (n := 12)
    (lo := (328968507 / 500000000)) (hi := (131587403 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((386161 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(386161 / 200000) = 1/(200000 / 386161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (328968507 / 500000000) (131587403 / 200000000) (Real.log (386161 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (386161 / 200000) = -Real.log (200000 / 386161) := by
    rw [show ((386161 / 200000) : ℝ) = ((200000 / 386161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2670826671 / 1000000000) ≤ -Real.log (13839 / 200000) ∧
    -Real.log (13839 / 200000) ≤ (106833067 / 40000000) := by
  have h := checkLog_sound (w := (11161 / 38839)) (n := 12)
    (lo := (591385131 / 1000000000)) (hi := (147846283 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 13839) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(25000 / 13839) = 1/(13839 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-106833067 / 40000000) (-2670826671 / 1000000000) (Real.log (13839 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (5144627 / 7812500) ≤ -Real.log (250000 / 482979) ∧
    -Real.log (250000 / 482979) ≤ (658512257 / 1000000000) := by
  have h := checkLog_sound (w := (232979 / 732979)) (n := 12)
    (lo := (5144627 / 7812500)) (hi := (658512257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((482979 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(482979 / 250000) = 1/(250000 / 482979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (5144627 / 7812500) (658512257 / 1000000000) (Real.log (482979 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (482979 / 250000) = -Real.log (250000 / 482979) := by
    rw [show ((482979 / 250000) : ℝ) = ((250000 / 482979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (33587663 / 12500000) ≤ -Real.log (17021 / 250000) ∧
    -Real.log (17021 / 250000) ≤ (671753261 / 250000000) := by
  have h := checkLog_sound (w := (14229 / 48271)) (n := 12)
    (lo := (1215143 / 2000000)) (hi := (607571501 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17021) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(31250 / 17021) = 1/(17021 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-671753261 / 250000000) (-33587663 / 12500000) (Real.log (17021 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3354549511 / 1000000000) ≤ -Real.log (250000000000 / 7158175662661) ∧
    -Real.log (250000000000 / 7158175662661) ≤ (838637379 / 250000000) := by
  have h := checkLog_sound (w := (3158175662661 / 11158175662661)) (n := 12)
    (lo := (581960791 / 1000000000)) (hi := (72745099 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7158175662661 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(7158175662661 / 4000000000000) = 1/(250000000000 / 7158175662661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3354549511 / 1000000000) (838637379 / 250000000) (Real.log (7158175662661 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (7158175662661 / 250000000000) = -Real.log (250000000000 / 7158175662661) := by
    rw [show ((7158175662661 / 250000000000) : ℝ) = ((250000000000 / 7158175662661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3370678749 / 1000000000) ≤ -Real.log (50000000000 / 1454913542717) ∧
    -Real.log (50000000000 / 1454913542717) ≤ (1685339377 / 500000000) := by
  have h := checkLog_sound (w := (654913542717 / 2254913542717)) (n := 12)
    (lo := (598090029 / 1000000000)) (hi := (59809003 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1454913542717 / 800000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1454913542717 / 800000000000) = 1/(50000000000 / 1454913542717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3370678749 / 1000000000) (1685339377 / 500000000) (Real.log (1454913542717 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1454913542717 / 50000000000) = -Real.log (50000000000 / 1454913542717) := by
    rw [show ((1454913542717 / 50000000000) : ℝ) = ((50000000000 / 1454913542717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (665752737 / 200000000) ≤ -Real.log (31250000000 / 871994454079) ∧
    -Real.log (31250000000 / 871994454079) ≤ (332876369 / 100000000) := by
  have h := checkLog_sound (w := (371994454079 / 1371994454079)) (n := 12)
    (lo := (111234993 / 200000000)) (hi := (278087483 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((871994454079 / 500000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(871994454079 / 500000000000) = 1/(31250000000 / 871994454079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (665752737 / 200000000) (332876369 / 100000000) (Real.log (871994454079 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (871994454079 / 31250000000) = -Real.log (31250000000 / 871994454079) := by
    rw [show ((871994454079 / 31250000000) : ℝ) = ((31250000000 / 871994454079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (209095331 / 62500000) ≤ -Real.log (250000000000 / 7093869337877) ∧
    -Real.log (250000000000 / 7093869337877) ≤ (3345525301 / 1000000000) := by
  have h := checkLog_sound (w := (3093869337877 / 11093869337877)) (n := 12)
    (lo := (4476067 / 7812500)) (hi := (572936577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7093869337877 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(7093869337877 / 4000000000000) = 1/(250000000000 / 7093869337877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (209095331 / 62500000) (3345525301 / 1000000000) (Real.log (7093869337877 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (7093869337877 / 250000000000) = -Real.log (250000000000 / 7093869337877) := by
    rw [show ((7093869337877 / 250000000000) : ℝ) = ((250000000000 / 7093869337877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0155

end


