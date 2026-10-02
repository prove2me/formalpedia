-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell010Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell010Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T15:57:08.605845+00:00
-- url     : https://prove2.me/theorems/e09a51bc-1d05-40ff-9278-ca4d47298a51
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell010Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell011…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell010Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell011Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell012Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell013Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell014Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell015Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell016Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell010Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell011Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell012Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell013Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell014Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell015Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell016Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell010Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell011Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell012Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell013Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell014Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell015Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell016Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell010Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell011Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell012Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell013Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell014Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell015Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell016Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell010Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell010
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

theorem reflection_log_1_neg : (228286553 / 1000000000) ≤ -Real.log (5120 / 6433) ∧
    -Real.log (5120 / 6433) ≤ (114143277 / 500000000) := by
  have h := checkLog_sound (w := (1313 / 11553)) (n := 12)
    (lo := (228286553 / 1000000000)) (hi := (114143277 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6433 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6433 / 5120) = 1/(5120 / 6433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (228286553 / 1000000000) (114143277 / 500000000) (Real.log (6433 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6433 / 5120) = -Real.log (5120 / 6433) := by
    rw [show ((6433 / 5120) : ℝ) = ((5120 / 6433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (296312961 / 1000000000) ≤ -Real.log (3807 / 5120) ∧
    -Real.log (3807 / 5120) ≤ (148156481 / 500000000) := by
  have h := checkLog_sound (w := (1313 / 8927)) (n := 12)
    (lo := (296312961 / 1000000000)) (hi := (148156481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3807) = 1/(3807 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-148156481 / 500000000) (-296312961 / 1000000000) (Real.log (3807 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (227820099 / 1000000000) ≤ -Real.log (512 / 643) ∧
    -Real.log (512 / 643) ≤ (2278201 / 10000000) := by
  have h := checkLog_sound (w := (131 / 1155)) (n := 12)
    (lo := (227820099 / 1000000000)) (hi := (2278201 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((643 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(643 / 512) = 1/(512 / 643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (227820099 / 1000000000) (2278201 / 10000000) (Real.log (643 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (643 / 512) = -Real.log (512 / 643) := by
    rw [show ((643 / 512) : ℝ) = ((512 / 643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (295525249 / 1000000000) ≤ -Real.log (381 / 512) ∧
    -Real.log (381 / 512) ≤ (1182101 / 4000000) := by
  have h := checkLog_sound (w := (131 / 893)) (n := 12)
    (lo := (295525249 / 1000000000)) (hi := (1182101 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 381) = 1/(381 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1182101 / 4000000) (-295525249 / 1000000000) (Real.log (381 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (166723029 / 1000000000) ≤ -Real.log (1000000 / 1181427) ∧
    -Real.log (1000000 / 1181427) ≤ (16672303 / 100000000) := by
  have h := checkLog_sound (w := (181427 / 2181427)) (n := 12)
    (lo := (166723029 / 1000000000)) (hi := (16672303 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1181427 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1181427 / 1000000) = 1/(1000000 / 1181427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (166723029 / 1000000000) (16672303 / 100000000) (Real.log (1181427 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1181427 / 1000000) = -Real.log (1000000 / 1181427) := by
    rw [show ((1181427 / 1000000) : ℝ) = ((1000000 / 1181427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (100096349 / 500000000) ≤ -Real.log (818573 / 1000000) ∧
    -Real.log (818573 / 1000000) ≤ (200192699 / 1000000000) := by
  have h := checkLog_sound (w := (181427 / 1818573)) (n := 12)
    (lo := (100096349 / 500000000)) (hi := (200192699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 818573) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 818573) = 1/(818573 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-200192699 / 1000000000) (-100096349 / 500000000) (Real.log (818573 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (83538811 / 500000000) ≤ -Real.log (500000 / 590923) ∧
    -Real.log (500000 / 590923) ≤ (167077623 / 1000000000) := by
  have h := checkLog_sound (w := (90923 / 1090923)) (n := 12)
    (lo := (83538811 / 500000000)) (hi := (167077623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((590923 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(590923 / 500000) = 1/(500000 / 590923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (83538811 / 500000000) (167077623 / 1000000000) (Real.log (590923 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (590923 / 500000) = -Real.log (500000 / 590923) := by
    rw [show ((590923 / 500000) : ℝ) = ((500000 / 590923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (25088087 / 125000000) ≤ -Real.log (409077 / 500000) ∧
    -Real.log (409077 / 500000) ≤ (200704697 / 1000000000) := by
  have h := checkLog_sound (w := (90923 / 909077)) (n := 12)
    (lo := (25088087 / 125000000)) (hi := (200704697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 409077) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 409077) = 1/(409077 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-200704697 / 1000000000) (-25088087 / 125000000) (Real.log (409077 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (12174761 / 100000000) ≤ -Real.log (1000000 / 1129469) ∧
    -Real.log (1000000 / 1129469) ≤ (121747611 / 1000000000) := by
  have h := checkLog_sound (w := (129469 / 2129469)) (n := 12)
    (lo := (12174761 / 100000000)) (hi := (121747611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1129469 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1129469 / 1000000) = 1/(1000000 / 1129469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (12174761 / 100000000) (121747611 / 1000000000) (Real.log (1129469 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1129469 / 1000000) = -Real.log (1000000 / 1129469) := by
    rw [show ((1129469 / 1000000) : ℝ) = ((1000000 / 1129469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (34662977 / 250000000) ≤ -Real.log (870531 / 1000000) ∧
    -Real.log (870531 / 1000000) ≤ (138651909 / 1000000000) := by
  have h := checkLog_sound (w := (129469 / 1870531)) (n := 12)
    (lo := (34662977 / 250000000)) (hi := (138651909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 870531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 870531) = 1/(870531 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-138651909 / 1000000000) (-34662977 / 250000000) (Real.log (870531 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (30504403 / 250000000) ≤ -Real.log (500000 / 564887) ∧
    -Real.log (500000 / 564887) ≤ (122017613 / 1000000000) := by
  have h := checkLog_sound (w := (64887 / 1064887)) (n := 12)
    (lo := (30504403 / 250000000)) (hi := (122017613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((564887 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(564887 / 500000) = 1/(500000 / 564887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (30504403 / 250000000) (122017613 / 1000000000) (Real.log (564887 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (564887 / 500000) = -Real.log (500000 / 564887) := by
    rw [show ((564887 / 500000) : ℝ) = ((500000 / 564887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (13900233 / 100000000) ≤ -Real.log (435113 / 500000) ∧
    -Real.log (435113 / 500000) ≤ (139002331 / 1000000000) := by
  have h := checkLog_sound (w := (64887 / 935113)) (n := 12)
    (lo := (13900233 / 100000000)) (hi := (139002331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 435113) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 435113) = 1/(435113 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-139002331 / 1000000000) (-13900233 / 100000000) (Real.log (435113 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (523345349 / 1000000000) ≤ -Real.log (500000000000 / 843832020997) ∧
    -Real.log (500000000000 / 843832020997) ≤ (10466907 / 20000000) := by
  have h := checkLog_sound (w := (343832020997 / 1343832020997)) (n := 12)
    (lo := (523345349 / 1000000000)) (hi := (10466907 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((843832020997 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(843832020997 / 500000000000) = 1/(500000000000 / 843832020997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (523345349 / 1000000000) (10466907 / 20000000) (Real.log (843832020997 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (843832020997 / 500000000000) = -Real.log (500000000000 / 843832020997) := by
    rw [show ((843832020997 / 500000000000) : ℝ) = ((500000000000 / 843832020997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (104919903 / 200000000) ≤ -Real.log (250000000000 / 422445495141) ∧
    -Real.log (250000000000 / 422445495141) ≤ (131149879 / 250000000) := by
  have h := checkLog_sound (w := (172445495141 / 672445495141)) (n := 12)
    (lo := (104919903 / 200000000)) (hi := (131149879 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((422445495141 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(422445495141 / 250000000000) = 1/(250000000000 / 422445495141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (104919903 / 200000000) (131149879 / 250000000) (Real.log (422445495141 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (422445495141 / 250000000000) = -Real.log (250000000000 / 422445495141) := by
    rw [show ((422445495141 / 250000000000) : ℝ) = ((250000000000 / 422445495141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (22932233 / 62500000) ≤ -Real.log (125000000000 / 180409535863) ∧
    -Real.log (125000000000 / 180409535863) ≤ (366915729 / 1000000000) := by
  have h := checkLog_sound (w := (55409535863 / 305409535863)) (n := 12)
    (lo := (22932233 / 62500000)) (hi := (366915729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((180409535863 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(180409535863 / 125000000000) = 1/(125000000000 / 180409535863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (22932233 / 62500000) (366915729 / 1000000000) (Real.log (180409535863 / 125000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (180409535863 / 125000000000) = -Real.log (125000000000 / 180409535863) := by
    rw [show ((180409535863 / 125000000000) : ℝ) = ((125000000000 / 180409535863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (183891159 / 500000000) ≤ -Real.log (500000000000 / 722263779191) ∧
    -Real.log (500000000000 / 722263779191) ≤ (367782319 / 1000000000) := by
  have h := checkLog_sound (w := (222263779191 / 1222263779191)) (n := 12)
    (lo := (183891159 / 500000000)) (hi := (367782319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((722263779191 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(722263779191 / 500000000000) = 1/(500000000000 / 722263779191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (183891159 / 500000000) (367782319 / 1000000000) (Real.log (722263779191 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (722263779191 / 500000000000) = -Real.log (500000000000 / 722263779191) := by
    rw [show ((722263779191 / 500000000000) : ℝ) = ((500000000000 / 722263779191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (260399519 / 1000000000) ≤ -Real.log (500000000000 / 648724169501) ∧
    -Real.log (500000000000 / 648724169501) ≤ (1627497 / 6250000) := by
  have h := checkLog_sound (w := (148724169501 / 1148724169501)) (n := 12)
    (lo := (260399519 / 1000000000)) (hi := (1627497 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((648724169501 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(648724169501 / 500000000000) = 1/(500000000000 / 648724169501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (260399519 / 1000000000) (1627497 / 6250000) (Real.log (648724169501 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (648724169501 / 500000000000) = -Real.log (500000000000 / 648724169501) := by
    rw [show ((648724169501 / 500000000000) : ℝ) = ((500000000000 / 648724169501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (261019943 / 1000000000) ≤ -Real.log (500000000000 / 649126778561) ∧
    -Real.log (500000000000 / 649126778561) ≤ (32627493 / 125000000) := by
  have h := checkLog_sound (w := (149126778561 / 1149126778561)) (n := 12)
    (lo := (261019943 / 1000000000)) (hi := (32627493 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((649126778561 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(649126778561 / 500000000000) = 1/(500000000000 / 649126778561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (261019943 / 1000000000) (32627493 / 125000000) (Real.log (649126778561 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (649126778561 / 500000000000) = -Real.log (500000000000 / 649126778561) := by
    rw [show ((649126778561 / 500000000000) : ℝ) = ((500000000000 / 649126778561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (8492359 / 500000000) ≤ -Real.log (245789677231 / 250000000000) ∧
    -Real.log (245789677231 / 250000000000) ≤ (16984719 / 1000000000) := by
  have h := checkLog_sound (w := (4210322769 / 495789677231)) (n := 12)
    (lo := (8492359 / 500000000)) (hi := (16984719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245789677231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245789677231) = 1/(245789677231 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-16984719 / 1000000000) (-8492359 / 500000000) (Real.log (245789677231 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (16904297 / 1000000000) ≤ -Real.log (983237778039 / 1000000000000) ∧
    -Real.log (983237778039 / 1000000000000) ≤ (8452149 / 500000000) := by
  have h := checkLog_sound (w := (16762221961 / 1983237778039)) (n := 12)
    (lo := (16904297 / 1000000000)) (hi := (8452149 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 983237778039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 983237778039) = 1/(983237778039 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-8452149 / 500000000) (-16904297 / 1000000000) (Real.log (983237778039 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell010

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell011Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell011
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

theorem reflection_log_1_neg : (22875279 / 100000000) ≤ -Real.log (1280 / 1609) ∧
    -Real.log (1280 / 1609) ≤ (228752791 / 1000000000) := by
  have h := checkLog_sound (w := (329 / 2889)) (n := 12)
    (lo := (22875279 / 100000000)) (hi := (228752791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1609 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1609 / 1280) = 1/(1280 / 1609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (22875279 / 100000000) (228752791 / 1000000000) (Real.log (1609 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1609 / 1280) = -Real.log (1280 / 1609) := by
    rw [show ((1609 / 1280) : ℝ) = ((1280 / 1609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (148550647 / 500000000) ≤ -Real.log (951 / 1280) ∧
    -Real.log (951 / 1280) ≤ (59420259 / 200000000) := by
  have h := checkLog_sound (w := (329 / 2231)) (n := 12)
    (lo := (148550647 / 500000000)) (hi := (59420259 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 951) = 1/(951 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-59420259 / 200000000) (-148550647 / 500000000) (Real.log (951 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (228286553 / 1000000000) ≤ -Real.log (5120 / 6433) ∧
    -Real.log (5120 / 6433) ≤ (114143277 / 500000000) := by
  have h := checkLog_sound (w := (1313 / 11553)) (n := 12)
    (lo := (228286553 / 1000000000)) (hi := (114143277 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6433 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6433 / 5120) = 1/(5120 / 6433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (228286553 / 1000000000) (114143277 / 500000000) (Real.log (6433 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6433 / 5120) = -Real.log (5120 / 6433) := by
    rw [show ((6433 / 5120) : ℝ) = ((5120 / 6433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (296312961 / 1000000000) ≤ -Real.log (3807 / 5120) ∧
    -Real.log (3807 / 5120) ≤ (148156481 / 500000000) := by
  have h := checkLog_sound (w := (1313 / 8927)) (n := 12)
    (lo := (296312961 / 1000000000)) (hi := (148156481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3807) = 1/(3807 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-148156481 / 500000000) (-296312961 / 1000000000) (Real.log (3807 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (20884597 / 125000000) ≤ -Real.log (200000 / 236369) ∧
    -Real.log (200000 / 236369) ≤ (167076777 / 1000000000) := by
  have h := checkLog_sound (w := (36369 / 436369)) (n := 12)
    (lo := (20884597 / 125000000)) (hi := (167076777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((236369 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(236369 / 200000) = 1/(200000 / 236369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (20884597 / 125000000) (167076777 / 1000000000) (Real.log (236369 / 200000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (236369 / 200000) = -Real.log (200000 / 236369) := by
    rw [show ((236369 / 200000) : ℝ) = ((200000 / 236369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (200703473 / 1000000000) ≤ -Real.log (163631 / 200000) ∧
    -Real.log (163631 / 200000) ≤ (100351737 / 500000000) := by
  have h := checkLog_sound (w := (36369 / 363631)) (n := 12)
    (lo := (200703473 / 1000000000)) (hi := (100351737 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 163631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 163631) = 1/(163631 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-100351737 / 500000000) (-200703473 / 1000000000) (Real.log (163631 / 200000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (41857811 / 250000000) ≤ -Real.log (125000 / 147783) ∧
    -Real.log (125000 / 147783) ≤ (33486249 / 200000000) := by
  have h := checkLog_sound (w := (22783 / 272783)) (n := 12)
    (lo := (41857811 / 250000000)) (hi := (33486249 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147783 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147783 / 125000) = 1/(125000 / 147783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (41857811 / 250000000) (33486249 / 200000000) (Real.log (147783 / 125000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (147783 / 125000) = -Real.log (125000 / 147783) := by
    rw [show ((147783 / 125000) : ℝ) = ((125000 / 147783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (50303933 / 250000000) ≤ -Real.log (102217 / 125000) ∧
    -Real.log (102217 / 125000) ≤ (201215733 / 1000000000) := by
  have h := checkLog_sound (w := (22783 / 227217)) (n := 12)
    (lo := (50303933 / 250000000)) (hi := (201215733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 102217) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 102217) = 1/(102217 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-201215733 / 1000000000) (-50303933 / 250000000) (Real.log (102217 / 125000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (122016727 / 1000000000) ≤ -Real.log (1000000 / 1129773) ∧
    -Real.log (1000000 / 1129773) ≤ (15252091 / 125000000) := by
  have h := checkLog_sound (w := (129773 / 2129773)) (n := 12)
    (lo := (122016727 / 1000000000)) (hi := (15252091 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1129773 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1129773 / 1000000) = 1/(1000000 / 1129773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (122016727 / 1000000000) (15252091 / 125000000) (Real.log (1129773 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1129773 / 1000000) = -Real.log (1000000 / 1129773) := by
    rw [show ((1129773 / 1000000) : ℝ) = ((1000000 / 1129773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (139001181 / 1000000000) ≤ -Real.log (870227 / 1000000) ∧
    -Real.log (870227 / 1000000) ≤ (69500591 / 500000000) := by
  have h := checkLog_sound (w := (129773 / 1870227)) (n := 12)
    (lo := (139001181 / 1000000000)) (hi := (69500591 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 870227) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 870227) = 1/(870227 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-69500591 / 500000000) (-139001181 / 1000000000) (Real.log (870227 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (1910729 / 15625000) ≤ -Real.log (500000 / 565039) ∧
    -Real.log (500000 / 565039) ≤ (122286657 / 1000000000) := by
  have h := checkLog_sound (w := (65039 / 1065039)) (n := 12)
    (lo := (1910729 / 15625000)) (hi := (122286657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((565039 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(565039 / 500000) = 1/(500000 / 565039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (1910729 / 15625000) (122286657 / 1000000000) (Real.log (565039 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (565039 / 500000) = -Real.log (500000 / 565039) := by
    rw [show ((565039 / 500000) : ℝ) = ((500000 / 565039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (69675863 / 500000000) ≤ -Real.log (434961 / 500000) ∧
    -Real.log (434961 / 500000) ≤ (139351727 / 1000000000) := by
  have h := checkLog_sound (w := (65039 / 934961)) (n := 12)
    (lo := (69675863 / 500000000)) (hi := (139351727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 434961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 434961) = 1/(434961 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-139351727 / 1000000000) (-69675863 / 500000000) (Real.log (434961 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (104919903 / 200000000) ≤ -Real.log (500000000000 / 844890990281) ∧
    -Real.log (500000000000 / 844890990281) ≤ (131149879 / 250000000) := by
  have h := checkLog_sound (w := (344890990281 / 1344890990281)) (n := 12)
    (lo := (104919903 / 200000000)) (hi := (131149879 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((844890990281 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(844890990281 / 500000000000) = 1/(500000000000 / 844890990281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (104919903 / 200000000) (131149879 / 250000000) (Real.log (844890990281 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (844890990281 / 500000000000) = -Real.log (500000000000 / 844890990281) := by
    rw [show ((844890990281 / 500000000000) : ℝ) = ((500000000000 / 844890990281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (131463521 / 250000000) ≤ -Real.log (62500000000 / 105743953733) ∧
    -Real.log (62500000000 / 105743953733) ≤ (105170817 / 200000000) := by
  have h := checkLog_sound (w := (43243953733 / 168243953733)) (n := 12)
    (lo := (131463521 / 250000000)) (hi := (105170817 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((105743953733 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(105743953733 / 62500000000) = 1/(62500000000 / 105743953733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (131463521 / 250000000) (105170817 / 200000000) (Real.log (105743953733 / 62500000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (105743953733 / 62500000000) = -Real.log (62500000000 / 105743953733) := by
    rw [show ((105743953733 / 62500000000) : ℝ) = ((62500000000 / 105743953733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (1471121 / 4000000) ≤ -Real.log (500000000000 / 722262285263) ∧
    -Real.log (500000000000 / 722262285263) ≤ (367780251 / 1000000000) := by
  have h := checkLog_sound (w := (222262285263 / 1222262285263)) (n := 12)
    (lo := (1471121 / 4000000)) (hi := (367780251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((722262285263 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(722262285263 / 500000000000) = 1/(500000000000 / 722262285263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (1471121 / 4000000) (367780251 / 1000000000) (Real.log (722262285263 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (722262285263 / 500000000000) = -Real.log (500000000000 / 722262285263) := by
    rw [show ((722262285263 / 500000000000) : ℝ) = ((500000000000 / 722262285263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (368646977 / 1000000000) ≤ -Real.log (125000000000 / 180722140153) ∧
    -Real.log (125000000000 / 180722140153) ≤ (184323489 / 500000000) := by
  have h := checkLog_sound (w := (55722140153 / 305722140153)) (n := 12)
    (lo := (368646977 / 1000000000)) (hi := (184323489 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((180722140153 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(180722140153 / 125000000000) = 1/(125000000000 / 180722140153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (368646977 / 1000000000) (184323489 / 500000000) (Real.log (180722140153 / 125000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (180722140153 / 125000000000) = -Real.log (125000000000 / 180722140153) := by
    rw [show ((180722140153 / 125000000000) : ℝ) = ((125000000000 / 180722140153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (261017909 / 1000000000) ≤ -Real.log (50000000000 / 64912545807) ∧
    -Real.log (50000000000 / 64912545807) ≤ (26101791 / 100000000) := by
  have h := checkLog_sound (w := (14912545807 / 114912545807)) (n := 12)
    (lo := (261017909 / 1000000000)) (hi := (26101791 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64912545807 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64912545807 / 50000000000) = 1/(50000000000 / 64912545807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (261017909 / 1000000000) (26101791 / 100000000) (Real.log (64912545807 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (64912545807 / 50000000000) = -Real.log (50000000000 / 64912545807) := by
    rw [show ((64912545807 / 50000000000) : ℝ) = ((50000000000 / 64912545807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (261638383 / 1000000000) ≤ -Real.log (500000000000 / 649528348519) ∧
    -Real.log (500000000000 / 649528348519) ≤ (16352399 / 62500000) := by
  have h := checkLog_sound (w := (149528348519 / 1149528348519)) (n := 12)
    (lo := (261638383 / 1000000000)) (hi := (16352399 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((649528348519 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(649528348519 / 500000000000) = 1/(500000000000 / 649528348519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (261638383 / 1000000000) (16352399 / 62500000) (Real.log (649528348519 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (649528348519 / 500000000000) = -Real.log (500000000000 / 649528348519) := by
    rw [show ((649528348519 / 500000000000) : ℝ) = ((500000000000 / 649528348519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (17065069 / 1000000000) ≤ -Real.log (245769928479 / 250000000000) ∧
    -Real.log (245769928479 / 250000000000) ≤ (1706507 / 100000000) := by
  have h := checkLog_sound (w := (4230071521 / 495769928479)) (n := 12)
    (lo := (17065069 / 1000000000)) (hi := (1706507 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245769928479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245769928479) = 1/(245769928479 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-1706507 / 100000000) (-17065069 / 1000000000) (Real.log (245769928479 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (8492227 / 500000000) ≤ -Real.log (983158968471 / 1000000000000) ∧
    -Real.log (983158968471 / 1000000000000) ≤ (3396891 / 200000000) := by
  have h := checkLog_sound (w := (16841031529 / 1983158968471)) (n := 12)
    (lo := (8492227 / 500000000)) (hi := (3396891 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 983158968471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 983158968471) = 1/(983158968471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-3396891 / 200000000) (-8492227 / 500000000) (Real.log (983158968471 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell011

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell012Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell012
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

theorem reflection_log_1_neg : (229218809 / 1000000000) ≤ -Real.log (5120 / 6439) ∧
    -Real.log (5120 / 6439) ≤ (22921881 / 100000000) := by
  have h := checkLog_sound (w := (1319 / 11559)) (n := 12)
    (lo := (229218809 / 1000000000)) (hi := (22921881 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6439 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6439 / 5120) = 1/(5120 / 6439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (229218809 / 1000000000) (22921881 / 100000000) (Real.log (6439 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6439 / 5120) = -Real.log (5120 / 6439) := by
    rw [show ((6439 / 5120) : ℝ) = ((5120 / 6439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (297890249 / 1000000000) ≤ -Real.log (3801 / 5120) ∧
    -Real.log (3801 / 5120) ≤ (1191561 / 4000000) := by
  have h := checkLog_sound (w := (1319 / 8921)) (n := 12)
    (lo := (297890249 / 1000000000)) (hi := (1191561 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3801) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3801) = 1/(3801 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1191561 / 4000000) (-297890249 / 1000000000) (Real.log (3801 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (22875279 / 100000000) ≤ -Real.log (1280 / 1609) ∧
    -Real.log (1280 / 1609) ≤ (228752791 / 1000000000) := by
  have h := checkLog_sound (w := (329 / 2889)) (n := 12)
    (lo := (22875279 / 100000000)) (hi := (228752791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1609 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1609 / 1280) = 1/(1280 / 1609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (22875279 / 100000000) (228752791 / 1000000000) (Real.log (1609 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1609 / 1280) = -Real.log (1280 / 1609) := by
    rw [show ((1609 / 1280) : ℝ) = ((1280 / 1609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (148550647 / 500000000) ≤ -Real.log (951 / 1280) ∧
    -Real.log (951 / 1280) ≤ (59420259 / 200000000) := by
  have h := checkLog_sound (w := (329 / 2231)) (n := 12)
    (lo := (148550647 / 500000000)) (hi := (59420259 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 951) = 1/(951 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-59420259 / 200000000) (-148550647 / 500000000) (Real.log (951 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (10464347 / 62500000) ≤ -Real.log (500000 / 591131) ∧
    -Real.log (500000 / 591131) ≤ (167429553 / 1000000000) := by
  have h := checkLog_sound (w := (91131 / 1091131)) (n := 12)
    (lo := (10464347 / 62500000)) (hi := (167429553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591131 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(591131 / 500000) = 1/(500000 / 591131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (10464347 / 62500000) (167429553 / 1000000000) (Real.log (591131 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (591131 / 500000) = -Real.log (500000 / 591131) := by
    rw [show ((591131 / 500000) : ℝ) = ((500000 / 591131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (201213287 / 1000000000) ≤ -Real.log (408869 / 500000) ∧
    -Real.log (408869 / 500000) ≤ (25151661 / 125000000) := by
  have h := checkLog_sound (w := (91131 / 908869)) (n := 12)
    (lo := (201213287 / 1000000000)) (hi := (25151661 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 408869) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 408869) = 1/(408869 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-25151661 / 125000000) (-201213287 / 1000000000) (Real.log (408869 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (33556779 / 200000000) ≤ -Real.log (1000000 / 1182681) ∧
    -Real.log (1000000 / 1182681) ≤ (20972987 / 125000000) := by
  have h := checkLog_sound (w := (182681 / 2182681)) (n := 12)
    (lo := (33556779 / 200000000)) (hi := (20972987 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1182681 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1182681 / 1000000) = 1/(1000000 / 1182681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (33556779 / 200000000) (20972987 / 125000000) (Real.log (1182681 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1182681 / 1000000) = -Real.log (1000000 / 1182681) := by
    rw [show ((1182681 / 1000000) : ℝ) = ((1000000 / 1182681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (201725807 / 1000000000) ≤ -Real.log (817319 / 1000000) ∧
    -Real.log (817319 / 1000000) ≤ (12607863 / 62500000) := by
  have h := checkLog_sound (w := (182681 / 1817319)) (n := 12)
    (lo := (201725807 / 1000000000)) (hi := (12607863 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 817319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 817319) = 1/(817319 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-12607863 / 62500000) (-201725807 / 1000000000) (Real.log (817319 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (122285771 / 1000000000) ≤ -Real.log (1000000 / 1130077) ∧
    -Real.log (1000000 / 1130077) ≤ (30571443 / 250000000) := by
  have h := checkLog_sound (w := (130077 / 2130077)) (n := 12)
    (lo := (122285771 / 1000000000)) (hi := (30571443 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1130077 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1130077 / 1000000) = 1/(1000000 / 1130077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (122285771 / 1000000000) (30571443 / 250000000) (Real.log (1130077 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1130077 / 1000000) = -Real.log (1000000 / 1130077) := by
    rw [show ((1130077 / 1000000) : ℝ) = ((1000000 / 1130077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (8709411 / 62500000) ≤ -Real.log (869923 / 1000000) ∧
    -Real.log (869923 / 1000000) ≤ (139350577 / 1000000000) := by
  have h := checkLog_sound (w := (130077 / 1869923)) (n := 12)
    (lo := (8709411 / 62500000)) (hi := (139350577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 869923) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 869923) = 1/(869923 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-139350577 / 1000000000) (-8709411 / 62500000) (Real.log (869923 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (15319343 / 125000000) ≤ -Real.log (1000000 / 1130381) ∧
    -Real.log (1000000 / 1130381) ≤ (24510949 / 200000000) := by
  have h := checkLog_sound (w := (130381 / 2130381)) (n := 12)
    (lo := (15319343 / 125000000)) (hi := (24510949 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1130381 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1130381 / 1000000) = 1/(1000000 / 1130381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (15319343 / 125000000) (24510949 / 200000000) (Real.log (1130381 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1130381 / 1000000) = -Real.log (1000000 / 1130381) := by
    rw [show ((1130381 / 1000000) : ℝ) = ((1000000 / 1130381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (69850047 / 500000000) ≤ -Real.log (869619 / 1000000) ∧
    -Real.log (869619 / 1000000) ≤ (27940019 / 200000000) := by
  have h := checkLog_sound (w := (130381 / 1869619)) (n := 12)
    (lo := (69850047 / 500000000)) (hi := (27940019 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 869619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 869619) = 1/(869619 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-27940019 / 200000000) (-69850047 / 500000000) (Real.log (869619 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (131463521 / 250000000) ≤ -Real.log (500000000000 / 845951629863) ∧
    -Real.log (500000000000 / 845951629863) ≤ (105170817 / 200000000) := by
  have h := checkLog_sound (w := (345951629863 / 1345951629863)) (n := 12)
    (lo := (131463521 / 250000000)) (hi := (105170817 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((845951629863 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(845951629863 / 500000000000) = 1/(500000000000 / 845951629863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (131463521 / 250000000) (105170817 / 200000000) (Real.log (845951629863 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (845951629863 / 500000000000) = -Real.log (500000000000 / 845951629863) := by
    rw [show ((845951629863 / 500000000000) : ℝ) = ((500000000000 / 845951629863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (263554529 / 500000000) ≤ -Real.log (5000000000 / 8470139437) ∧
    -Real.log (5000000000 / 8470139437) ≤ (527109059 / 1000000000) := by
  have h := checkLog_sound (w := (3470139437 / 13470139437)) (n := 12)
    (lo := (263554529 / 500000000)) (hi := (527109059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8470139437 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8470139437 / 5000000000) = 1/(5000000000 / 8470139437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (263554529 / 500000000) (527109059 / 1000000000) (Real.log (8470139437 / 5000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (8470139437 / 5000000000) = -Real.log (5000000000 / 8470139437) := by
    rw [show ((8470139437 / 5000000000) : ℝ) = ((5000000000 / 8470139437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (368642839 / 1000000000) ≤ -Real.log (100000000000 / 144577113941) ∧
    -Real.log (100000000000 / 144577113941) ≤ (9216071 / 25000000) := by
  have h := checkLog_sound (w := (44577113941 / 244577113941)) (n := 12)
    (lo := (368642839 / 1000000000)) (hi := (9216071 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((144577113941 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(144577113941 / 100000000000) = 1/(100000000000 / 144577113941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (368642839 / 1000000000) (9216071 / 25000000) (Real.log (144577113941 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (144577113941 / 100000000000) = -Real.log (100000000000 / 144577113941) := by
    rw [show ((144577113941 / 100000000000) : ℝ) = ((100000000000 / 144577113941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (184754851 / 500000000) ≤ -Real.log (50000000000 / 72351248411) ∧
    -Real.log (50000000000 / 72351248411) ≤ (369509703 / 1000000000) := by
  have h := checkLog_sound (w := (22351248411 / 122351248411)) (n := 12)
    (lo := (184754851 / 500000000)) (hi := (369509703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((72351248411 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(72351248411 / 50000000000) = 1/(50000000000 / 72351248411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (184754851 / 500000000) (369509703 / 1000000000) (Real.log (72351248411 / 50000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (72351248411 / 50000000000) = -Real.log (50000000000 / 72351248411) := by
    rw [show ((72351248411 / 50000000000) : ℝ) = ((50000000000 / 72351248411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (65409087 / 250000000) ≤ -Real.log (15625000000 / 20297719597) ∧
    -Real.log (15625000000 / 20297719597) ≤ (261636349 / 1000000000) := by
  have h := checkLog_sound (w := (4672719597 / 35922719597)) (n := 12)
    (lo := (65409087 / 250000000)) (hi := (261636349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20297719597 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20297719597 / 15625000000) = 1/(15625000000 / 20297719597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (65409087 / 250000000) (261636349 / 1000000000) (Real.log (20297719597 / 15625000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (20297719597 / 15625000000) = -Real.log (15625000000 / 20297719597) := by
    rw [show ((20297719597 / 15625000000) : ℝ) = ((15625000000 / 20297719597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (131127419 / 500000000) ≤ -Real.log (500000000000 / 649928876899) ∧
    -Real.log (500000000000 / 649928876899) ≤ (262254839 / 1000000000) := by
  have h := checkLog_sound (w := (149928876899 / 1149928876899)) (n := 12)
    (lo := (131127419 / 500000000)) (hi := (262254839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((649928876899 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(649928876899 / 500000000000) = 1/(500000000000 / 649928876899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (131127419 / 500000000) (262254839 / 1000000000) (Real.log (649928876899 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (649928876899 / 500000000000) = -Real.log (500000000000 / 649928876899) := by
    rw [show ((649928876899 / 500000000000) : ℝ) = ((500000000000 / 649928876899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (342907 / 20000000) ≤ -Real.log (983000794839 / 1000000000000) ∧
    -Real.log (983000794839 / 1000000000000) ≤ (17145351 / 1000000000) := by
  have h := checkLog_sound (w := (16999205161 / 1983000794839)) (n := 12)
    (lo := (342907 / 20000000)) (hi := (17145351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 983000794839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 983000794839) = 1/(983000794839 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-17145351 / 1000000000) (-342907 / 20000000) (Real.log (983000794839 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (3412961 / 200000000) ≤ -Real.log (983079974071 / 1000000000000) ∧
    -Real.log (983079974071 / 1000000000000) ≤ (8532403 / 500000000) := by
  have h := checkLog_sound (w := (16920025929 / 1983079974071)) (n := 12)
    (lo := (3412961 / 200000000)) (hi := (8532403 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 983079974071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 983079974071) = 1/(983079974071 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-8532403 / 500000000) (-3412961 / 200000000) (Real.log (983079974071 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell012

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell013Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell013
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

theorem reflection_log_1_neg : (229684611 / 1000000000) ≤ -Real.log (2560 / 3221) ∧
    -Real.log (2560 / 3221) ≤ (57421153 / 250000000) := by
  have h := checkLog_sound (w := (661 / 5781)) (n := 12)
    (lo := (229684611 / 1000000000)) (hi := (57421153 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3221 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3221 / 2560) = 1/(2560 / 3221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (229684611 / 1000000000) (57421153 / 250000000) (Real.log (3221 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3221 / 2560) = -Real.log (2560 / 3221) := by
    rw [show ((3221 / 2560) : ℝ) = ((2560 / 3221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (149339913 / 500000000) ≤ -Real.log (1899 / 2560) ∧
    -Real.log (1899 / 2560) ≤ (298679827 / 1000000000) := by
  have h := checkLog_sound (w := (661 / 4459)) (n := 12)
    (lo := (149339913 / 500000000)) (hi := (298679827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1899) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1899) = 1/(1899 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-298679827 / 1000000000) (-149339913 / 500000000) (Real.log (1899 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (229218809 / 1000000000) ≤ -Real.log (5120 / 6439) ∧
    -Real.log (5120 / 6439) ≤ (22921881 / 100000000) := by
  have h := checkLog_sound (w := (1319 / 11559)) (n := 12)
    (lo := (229218809 / 1000000000)) (hi := (22921881 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6439 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6439 / 5120) = 1/(5120 / 6439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (229218809 / 1000000000) (22921881 / 100000000) (Real.log (6439 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6439 / 5120) = -Real.log (5120 / 6439) := by
    rw [show ((6439 / 5120) : ℝ) = ((5120 / 6439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (297890249 / 1000000000) ≤ -Real.log (3801 / 5120) ∧
    -Real.log (3801 / 5120) ≤ (1191561 / 4000000) := by
  have h := checkLog_sound (w := (1319 / 8921)) (n := 12)
    (lo := (297890249 / 1000000000)) (hi := (1191561 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3801) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3801) = 1/(3801 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1191561 / 4000000) (-297890249 / 1000000000) (Real.log (3801 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (167783049 / 1000000000) ≤ -Real.log (25000 / 29567) ∧
    -Real.log (25000 / 29567) ≤ (3355661 / 20000000) := by
  have h := checkLog_sound (w := (4567 / 54567)) (n := 12)
    (lo := (167783049 / 1000000000)) (hi := (3355661 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29567 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29567 / 25000) = 1/(25000 / 29567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (167783049 / 1000000000) (3355661 / 20000000) (Real.log (29567 / 25000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (29567 / 25000) = -Real.log (25000 / 29567) := by
    rw [show ((29567 / 25000) : ℝ) = ((25000 / 29567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (201724583 / 1000000000) ≤ -Real.log (20433 / 25000) ∧
    -Real.log (20433 / 25000) ≤ (25215573 / 125000000) := by
  have h := checkLog_sound (w := (4567 / 45433)) (n := 12)
    (lo := (201724583 / 1000000000)) (hi := (25215573 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 20433) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 20433) = 1/(20433 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-25215573 / 125000000) (-201724583 / 1000000000) (Real.log (20433 / 25000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (168137267 / 1000000000) ≤ -Real.log (1000000 / 1183099) ∧
    -Real.log (1000000 / 1183099) ≤ (42034317 / 250000000) := by
  have h := checkLog_sound (w := (183099 / 2183099)) (n := 12)
    (lo := (168137267 / 1000000000)) (hi := (42034317 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1183099 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1183099 / 1000000) = 1/(1000000 / 1183099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (168137267 / 1000000000) (42034317 / 250000000) (Real.log (1183099 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1183099 / 1000000) = -Real.log (1000000 / 1183099) := by
    rw [show ((1183099 / 1000000) : ℝ) = ((1000000 / 1183099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (101118683 / 500000000) ≤ -Real.log (816901 / 1000000) ∧
    -Real.log (816901 / 1000000) ≤ (202237367 / 1000000000) := by
  have h := checkLog_sound (w := (183099 / 1816901)) (n := 12)
    (lo := (101118683 / 500000000)) (hi := (202237367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 816901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 816901) = 1/(816901 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-202237367 / 1000000000) (-101118683 / 500000000) (Real.log (816901 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (122553859 / 1000000000) ≤ -Real.log (50000 / 56519) ∧
    -Real.log (50000 / 56519) ≤ (6127693 / 50000000) := by
  have h := checkLog_sound (w := (6519 / 106519)) (n := 12)
    (lo := (122553859 / 1000000000)) (hi := (6127693 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((56519 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(56519 / 50000) = 1/(50000 / 56519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (122553859 / 1000000000) (6127693 / 50000000) (Real.log (56519 / 50000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (56519 / 50000) = -Real.log (50000 / 56519) := by
    rw [show ((56519 / 50000) : ℝ) = ((50000 / 56519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (545699 / 3906250) ≤ -Real.log (43481 / 50000) ∧
    -Real.log (43481 / 50000) ≤ (27939789 / 200000000) := by
  have h := checkLog_sound (w := (6519 / 93481)) (n := 12)
    (lo := (545699 / 3906250)) (hi := (27939789 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 43481) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 43481) = 1/(43481 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-27939789 / 200000000) (-545699 / 3906250) (Real.log (43481 / 50000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (122823643 / 1000000000) ≤ -Real.log (200000 / 226137) ∧
    -Real.log (200000 / 226137) ≤ (30705911 / 250000000) := by
  have h := checkLog_sound (w := (26137 / 426137)) (n := 12)
    (lo := (122823643 / 1000000000)) (hi := (30705911 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((226137 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(226137 / 200000) = 1/(200000 / 226137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (122823643 / 1000000000) (30705911 / 250000000) (Real.log (226137 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (226137 / 200000) = -Real.log (200000 / 226137) := by
    rw [show ((226137 / 200000) : ℝ) = ((200000 / 226137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (140049733 / 1000000000) ≤ -Real.log (173863 / 200000) ∧
    -Real.log (173863 / 200000) ≤ (70024867 / 500000000) := by
  have h := checkLog_sound (w := (26137 / 373863)) (n := 12)
    (lo := (140049733 / 1000000000)) (hi := (70024867 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 173863) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 173863) = 1/(173863 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-70024867 / 500000000) (-140049733 / 1000000000) (Real.log (173863 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (263554529 / 500000000) ≤ -Real.log (500000000000 / 847013943699) ∧
    -Real.log (500000000000 / 847013943699) ≤ (527109059 / 1000000000) := by
  have h := checkLog_sound (w := (347013943699 / 1347013943699)) (n := 12)
    (lo := (263554529 / 500000000)) (hi := (527109059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((847013943699 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(847013943699 / 500000000000) = 1/(500000000000 / 847013943699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (263554529 / 500000000) (527109059 / 1000000000) (Real.log (847013943699 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (847013943699 / 500000000000) = -Real.log (500000000000 / 847013943699) := by
    rw [show ((847013943699 / 500000000000) : ℝ) = ((500000000000 / 847013943699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (264182219 / 500000000) ≤ -Real.log (125000000000 / 212019483939) ∧
    -Real.log (125000000000 / 212019483939) ≤ (528364439 / 1000000000) := by
  have h := checkLog_sound (w := (87019483939 / 337019483939)) (n := 12)
    (lo := (264182219 / 500000000)) (hi := (528364439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((212019483939 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(212019483939 / 125000000000) = 1/(125000000000 / 212019483939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (264182219 / 500000000) (528364439 / 1000000000) (Real.log (212019483939 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (212019483939 / 125000000000) = -Real.log (125000000000 / 212019483939) := by
    rw [show ((212019483939 / 125000000000) : ℝ) = ((125000000000 / 212019483939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (369507633 / 1000000000) ≤ -Real.log (62500000000 / 90438873391) ∧
    -Real.log (62500000000 / 90438873391) ≤ (184753817 / 500000000) := by
  have h := checkLog_sound (w := (27938873391 / 152938873391)) (n := 12)
    (lo := (369507633 / 1000000000)) (hi := (184753817 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((90438873391 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(90438873391 / 62500000000) = 1/(62500000000 / 90438873391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (369507633 / 1000000000) (184753817 / 500000000) (Real.log (90438873391 / 62500000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (90438873391 / 62500000000) = -Real.log (62500000000 / 90438873391) := by
    rw [show ((90438873391 / 62500000000) : ℝ) = ((62500000000 / 90438873391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (370374633 / 1000000000) ≤ -Real.log (244140625 / 353583273) ∧
    -Real.log (244140625 / 353583273) ≤ (185187317 / 500000000) := by
  have h := checkLog_sound (w := (54721324 / 298861949)) (n := 12)
    (lo := (370374633 / 1000000000)) (hi := (185187317 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((353583273 / 244140625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(353583273 / 244140625) = 1/(244140625 / 353583273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (370374633 / 1000000000) (185187317 / 500000000) (Real.log (353583273 / 244140625)) := by
  have h := reflection_log_16_neg
  have he : Real.log (353583273 / 244140625) = -Real.log (244140625 / 353583273) := by
    rw [show ((353583273 / 244140625) : ℝ) = ((244140625 / 353583273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (262252803 / 1000000000) ≤ -Real.log (125000000000 / 162481888641) ∧
    -Real.log (125000000000 / 162481888641) ≤ (65563201 / 250000000) := by
  have h := checkLog_sound (w := (37481888641 / 287481888641)) (n := 12)
    (lo := (262252803 / 1000000000)) (hi := (65563201 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((162481888641 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(162481888641 / 125000000000) = 1/(125000000000 / 162481888641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (262252803 / 1000000000) (65563201 / 250000000) (Real.log (162481888641 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (162481888641 / 125000000000) = -Real.log (125000000000 / 162481888641) := by
    rw [show ((162481888641 / 125000000000) : ℝ) = ((125000000000 / 162481888641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (262873377 / 1000000000) ≤ -Real.log (125000000000 / 162582751937) ∧
    -Real.log (125000000000 / 162582751937) ≤ (131436689 / 500000000) := by
  have h := checkLog_sound (w := (37582751937 / 287582751937)) (n := 12)
    (lo := (262873377 / 1000000000)) (hi := (131436689 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((162582751937 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(162582751937 / 125000000000) = 1/(125000000000 / 162582751937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (262873377 / 1000000000) (131436689 / 500000000) (Real.log (162582751937 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (162582751937 / 125000000000) = -Real.log (125000000000 / 162582751937) := by
    rw [show ((162582751937 / 125000000000) : ℝ) = ((125000000000 / 162582751937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1722609 / 100000000) ≤ -Real.log (39316857231 / 40000000000) ∧
    -Real.log (39316857231 / 40000000000) ≤ (17226091 / 1000000000) := by
  have h := checkLog_sound (w := (683142769 / 79316857231)) (n := 12)
    (lo := (1722609 / 100000000)) (hi := (17226091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39316857231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39316857231) = 1/(39316857231 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-17226091 / 1000000000) (-1722609 / 100000000) (Real.log (39316857231 / 40000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (4286271 / 250000000) ≤ -Real.log (2457502639 / 2500000000) ∧
    -Real.log (2457502639 / 2500000000) ≤ (3429017 / 200000000) := by
  have h := checkLog_sound (w := (42497361 / 4957502639)) (n := 12)
    (lo := (4286271 / 250000000)) (hi := (3429017 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2457502639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2457502639) = 1/(2457502639 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-3429017 / 200000000) (-4286271 / 250000000) (Real.log (2457502639 / 2500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell013

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell014Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell014
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

theorem reflection_log_1_neg : (230150197 / 1000000000) ≤ -Real.log (1024 / 1289) ∧
    -Real.log (1024 / 1289) ≤ (115075099 / 500000000) := by
  have h := checkLog_sound (w := (265 / 2313)) (n := 12)
    (lo := (230150197 / 1000000000)) (hi := (115075099 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1289 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1289 / 1024) = 1/(1024 / 1289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (230150197 / 1000000000) (115075099 / 500000000) (Real.log (1289 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1289 / 1024) = -Real.log (1024 / 1289) := by
    rw [show ((1289 / 1024) : ℝ) = ((1024 / 1289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (74867507 / 250000000) ≤ -Real.log (759 / 1024) ∧
    -Real.log (759 / 1024) ≤ (299470029 / 1000000000) := by
  have h := checkLog_sound (w := (265 / 1783)) (n := 12)
    (lo := (74867507 / 250000000)) (hi := (299470029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 759) = 1/(759 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-299470029 / 1000000000) (-74867507 / 250000000) (Real.log (759 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (229684611 / 1000000000) ≤ -Real.log (2560 / 3221) ∧
    -Real.log (2560 / 3221) ≤ (57421153 / 250000000) := by
  have h := checkLog_sound (w := (661 / 5781)) (n := 12)
    (lo := (229684611 / 1000000000)) (hi := (57421153 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3221 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3221 / 2560) = 1/(2560 / 3221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (229684611 / 1000000000) (57421153 / 250000000) (Real.log (3221 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3221 / 2560) = -Real.log (2560 / 3221) := by
    rw [show ((3221 / 2560) : ℝ) = ((2560 / 3221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (149339913 / 500000000) ≤ -Real.log (1899 / 2560) ∧
    -Real.log (1899 / 2560) ≤ (298679827 / 1000000000) := by
  have h := checkLog_sound (w := (661 / 4459)) (n := 12)
    (lo := (149339913 / 500000000)) (hi := (298679827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1899) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1899) = 1/(1899 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-298679827 / 1000000000) (-149339913 / 500000000) (Real.log (1899 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (168136421 / 1000000000) ≤ -Real.log (500000 / 591549) ∧
    -Real.log (500000 / 591549) ≤ (84068211 / 500000000) := by
  have h := checkLog_sound (w := (91549 / 1091549)) (n := 12)
    (lo := (168136421 / 1000000000)) (hi := (84068211 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591549 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(591549 / 500000) = 1/(500000 / 591549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (168136421 / 1000000000) (84068211 / 500000000) (Real.log (591549 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (591549 / 500000) = -Real.log (500000 / 591549) := by
    rw [show ((591549 / 500000) : ℝ) = ((500000 / 591549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (101118071 / 500000000) ≤ -Real.log (408451 / 500000) ∧
    -Real.log (408451 / 500000) ≤ (202236143 / 1000000000) := by
  have h := checkLog_sound (w := (91549 / 908451)) (n := 12)
    (lo := (101118071 / 500000000)) (hi := (202236143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 408451) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 408451) = 1/(408451 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-202236143 / 1000000000) (-101118071 / 500000000) (Real.log (408451 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (84245257 / 500000000) ≤ -Real.log (1000000 / 1183517) ∧
    -Real.log (1000000 / 1183517) ≤ (33698103 / 200000000) := by
  have h := checkLog_sound (w := (183517 / 2183517)) (n := 12)
    (lo := (84245257 / 500000000)) (hi := (33698103 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1183517 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1183517 / 1000000) = 1/(1000000 / 1183517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (84245257 / 500000000) (33698103 / 200000000) (Real.log (1183517 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1183517 / 1000000) = -Real.log (1000000 / 1183517) := by
    rw [show ((1183517 / 1000000) : ℝ) = ((1000000 / 1183517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (202749187 / 1000000000) ≤ -Real.log (816483 / 1000000) ∧
    -Real.log (816483 / 1000000) ≤ (50687297 / 250000000) := by
  have h := checkLog_sound (w := (183517 / 1816483)) (n := 12)
    (lo := (202749187 / 1000000000)) (hi := (50687297 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 816483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 816483) = 1/(816483 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-50687297 / 250000000) (-202749187 / 1000000000) (Real.log (816483 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (122822759 / 1000000000) ≤ -Real.log (250000 / 282671) ∧
    -Real.log (250000 / 282671) ≤ (3070569 / 25000000) := by
  have h := checkLog_sound (w := (32671 / 532671)) (n := 12)
    (lo := (122822759 / 1000000000)) (hi := (3070569 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((282671 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(282671 / 250000) = 1/(250000 / 282671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (122822759 / 1000000000) (3070569 / 25000000) (Real.log (282671 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (282671 / 250000) = -Real.log (250000 / 282671) := by
    rw [show ((282671 / 250000) : ℝ) = ((250000 / 282671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (140048583 / 1000000000) ≤ -Real.log (217329 / 250000) ∧
    -Real.log (217329 / 250000) ≤ (17506073 / 125000000) := by
  have h := checkLog_sound (w := (32671 / 467329)) (n := 12)
    (lo := (140048583 / 1000000000)) (hi := (17506073 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 217329) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 217329) = 1/(217329 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-17506073 / 125000000) (-140048583 / 1000000000) (Real.log (217329 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (123092471 / 1000000000) ≤ -Real.log (1000000 / 1130989) ∧
    -Real.log (1000000 / 1130989) ≤ (15386559 / 125000000) := by
  have h := checkLog_sound (w := (130989 / 2130989)) (n := 12)
    (lo := (123092471 / 1000000000)) (hi := (15386559 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1130989 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1130989 / 1000000) = 1/(1000000 / 1130989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (123092471 / 1000000000) (15386559 / 125000000) (Real.log (1130989 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1130989 / 1000000) = -Real.log (1000000 / 1130989) := by
    rw [show ((1130989 / 1000000) : ℝ) = ((1000000 / 1130989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (28079899 / 200000000) ≤ -Real.log (869011 / 1000000) ∧
    -Real.log (869011 / 1000000) ≤ (17549937 / 125000000) := by
  have h := checkLog_sound (w := (130989 / 1869011)) (n := 12)
    (lo := (28079899 / 200000000)) (hi := (17549937 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 869011) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 869011) = 1/(869011 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-17549937 / 125000000) (-28079899 / 200000000) (Real.log (869011 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (264182219 / 500000000) ≤ -Real.log (100000000000 / 169615587151) ∧
    -Real.log (100000000000 / 169615587151) ≤ (528364439 / 1000000000) := by
  have h := checkLog_sound (w := (69615587151 / 269615587151)) (n := 12)
    (lo := (264182219 / 500000000)) (hi := (528364439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169615587151 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169615587151 / 100000000000) = 1/(100000000000 / 169615587151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (264182219 / 500000000) (528364439 / 1000000000) (Real.log (169615587151 / 100000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (169615587151 / 100000000000) = -Real.log (100000000000 / 169615587151) := by
    rw [show ((169615587151 / 100000000000) : ℝ) = ((100000000000 / 169615587151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (21184809 / 40000000) ≤ -Real.log (250000000000 / 424571805007) ∧
    -Real.log (250000000000 / 424571805007) ≤ (264810113 / 500000000) := by
  have h := checkLog_sound (w := (174571805007 / 674571805007)) (n := 12)
    (lo := (21184809 / 40000000)) (hi := (264810113 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((424571805007 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(424571805007 / 250000000000) = 1/(250000000000 / 424571805007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (21184809 / 40000000) (264810113 / 500000000) (Real.log (424571805007 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (424571805007 / 250000000000) = -Real.log (250000000000 / 424571805007) := by
    rw [show ((424571805007 / 250000000000) : ℝ) = ((250000000000 / 424571805007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (92593141 / 250000000) ≤ -Real.log (50000000000 / 72413704459) ∧
    -Real.log (50000000000 / 72413704459) ≤ (74074513 / 200000000) := by
  have h := checkLog_sound (w := (22413704459 / 122413704459)) (n := 12)
    (lo := (92593141 / 250000000)) (hi := (74074513 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((72413704459 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(72413704459 / 50000000000) = 1/(50000000000 / 72413704459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (92593141 / 250000000) (74074513 / 200000000) (Real.log (72413704459 / 50000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (72413704459 / 50000000000) = -Real.log (50000000000 / 72413704459) := by
    rw [show ((72413704459 / 50000000000) : ℝ) = ((50000000000 / 72413704459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (371239701 / 1000000000) ≤ -Real.log (500000000000 / 724765243123) ∧
    -Real.log (500000000000 / 724765243123) ≤ (185619851 / 500000000) := by
  have h := checkLog_sound (w := (224765243123 / 1224765243123)) (n := 12)
    (lo := (371239701 / 1000000000)) (hi := (185619851 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((724765243123 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(724765243123 / 500000000000) = 1/(500000000000 / 724765243123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (371239701 / 1000000000) (185619851 / 500000000) (Real.log (724765243123 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (724765243123 / 500000000000) = -Real.log (500000000000 / 724765243123) := by
    rw [show ((724765243123 / 500000000000) : ℝ) = ((500000000000 / 724765243123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (131435671 / 500000000) ≤ -Real.log (500000000000 / 650329684487) ∧
    -Real.log (500000000000 / 650329684487) ≤ (262871343 / 1000000000) := by
  have h := checkLog_sound (w := (150329684487 / 1150329684487)) (n := 12)
    (lo := (131435671 / 500000000)) (hi := (262871343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((650329684487 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(650329684487 / 500000000000) = 1/(500000000000 / 650329684487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (131435671 / 500000000) (262871343 / 1000000000) (Real.log (650329684487 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (650329684487 / 500000000000) = -Real.log (500000000000 / 650329684487) := by
    rw [show ((650329684487 / 500000000000) : ℝ) = ((500000000000 / 650329684487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (131745983 / 500000000) ≤ -Real.log (250000000000 / 325366709973) ∧
    -Real.log (250000000000 / 325366709973) ≤ (263491967 / 1000000000) := by
  have h := checkLog_sound (w := (75366709973 / 575366709973)) (n := 12)
    (lo := (131745983 / 500000000)) (hi := (263491967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((325366709973 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(325366709973 / 250000000000) = 1/(250000000000 / 325366709973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (131745983 / 500000000) (263491967 / 1000000000) (Real.log (325366709973 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (325366709973 / 250000000000) = -Real.log (250000000000 / 325366709973) := by
    rw [show ((325366709973 / 250000000000) : ℝ) = ((250000000000 / 325366709973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1081689 / 62500000) ≤ -Real.log (982841881879 / 1000000000000) ∧
    -Real.log (982841881879 / 1000000000000) ≤ (692281 / 40000000) := by
  have h := checkLog_sound (w := (17158118121 / 1982841881879)) (n := 12)
    (lo := (1081689 / 62500000)) (hi := (692281 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 982841881879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 982841881879) = 1/(982841881879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-692281 / 40000000) (-1081689 / 62500000) (Real.log (982841881879 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (538307 / 31250000) ≤ -Real.log (61432605759 / 62500000000) ∧
    -Real.log (61432605759 / 62500000000) ≤ (689033 / 40000000) := by
  have h := checkLog_sound (w := (1067394241 / 123932605759)) (n := 12)
    (lo := (538307 / 31250000)) (hi := (689033 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61432605759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61432605759) = 1/(61432605759 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-689033 / 40000000) (-538307 / 31250000) (Real.log (61432605759 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell014

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell015Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell015
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

theorem reflection_log_1_neg : (115307783 / 500000000) ≤ -Real.log (320 / 403) ∧
    -Real.log (320 / 403) ≤ (230615567 / 1000000000) := by
  have h := checkLog_sound (w := (83 / 723)) (n := 12)
    (lo := (115307783 / 500000000)) (hi := (230615567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((403 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(403 / 320) = 1/(320 / 403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (115307783 / 500000000) (230615567 / 1000000000) (Real.log (403 / 320)) := by
  have h := reflection_log_1_neg
  have he : Real.log (403 / 320) = -Real.log (320 / 403) := by
    rw [show ((403 / 320) : ℝ) = ((320 / 403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (150130427 / 500000000) ≤ -Real.log (237 / 320) ∧
    -Real.log (237 / 320) ≤ (60052171 / 200000000) := by
  have h := checkLog_sound (w := (83 / 557)) (n := 12)
    (lo := (150130427 / 500000000)) (hi := (60052171 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 237) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 237) = 1/(237 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-60052171 / 200000000) (-150130427 / 500000000) (Real.log (237 / 320)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (230150197 / 1000000000) ≤ -Real.log (1024 / 1289) ∧
    -Real.log (1024 / 1289) ≤ (115075099 / 500000000) := by
  have h := checkLog_sound (w := (265 / 2313)) (n := 12)
    (lo := (230150197 / 1000000000)) (hi := (115075099 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1289 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1289 / 1024) = 1/(1024 / 1289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (230150197 / 1000000000) (115075099 / 500000000) (Real.log (1289 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1289 / 1024) = -Real.log (1024 / 1289) := by
    rw [show ((1289 / 1024) : ℝ) = ((1024 / 1289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (74867507 / 250000000) ≤ -Real.log (759 / 1024) ∧
    -Real.log (759 / 1024) ≤ (299470029 / 1000000000) := by
  have h := checkLog_sound (w := (265 / 1783)) (n := 12)
    (lo := (74867507 / 250000000)) (hi := (299470029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 759) = 1/(759 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-299470029 / 1000000000) (-74867507 / 250000000) (Real.log (759 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (168489669 / 1000000000) ≤ -Real.log (250000 / 295879) ∧
    -Real.log (250000 / 295879) ≤ (16848967 / 100000000) := by
  have h := checkLog_sound (w := (45879 / 545879)) (n := 12)
    (lo := (168489669 / 1000000000)) (hi := (16848967 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((295879 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(295879 / 250000) = 1/(250000 / 295879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (168489669 / 1000000000) (16848967 / 100000000) (Real.log (295879 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (295879 / 250000) = -Real.log (250000 / 295879) := by
    rw [show ((295879 / 250000) : ℝ) = ((250000 / 295879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (101373981 / 500000000) ≤ -Real.log (204121 / 250000) ∧
    -Real.log (204121 / 250000) ≤ (202747963 / 1000000000) := by
  have h := checkLog_sound (w := (45879 / 454121)) (n := 12)
    (lo := (101373981 / 500000000)) (hi := (202747963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 204121) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 204121) = 1/(204121 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-202747963 / 1000000000) (-101373981 / 500000000) (Real.log (204121 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (42210909 / 250000000) ≤ -Real.log (200000 / 236787) ∧
    -Real.log (200000 / 236787) ≤ (168843637 / 1000000000) := by
  have h := checkLog_sound (w := (36787 / 436787)) (n := 12)
    (lo := (42210909 / 250000000)) (hi := (168843637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((236787 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(236787 / 200000) = 1/(200000 / 236787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (42210909 / 250000000) (168843637 / 1000000000) (Real.log (236787 / 200000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (236787 / 200000) = -Real.log (200000 / 236787) := by
    rw [show ((236787 / 200000) : ℝ) = ((200000 / 236787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (20326127 / 100000000) ≤ -Real.log (163213 / 200000) ∧
    -Real.log (163213 / 200000) ≤ (203261271 / 1000000000) := by
  have h := checkLog_sound (w := (36787 / 363213)) (n := 12)
    (lo := (20326127 / 100000000)) (hi := (203261271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 163213) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 163213) = 1/(163213 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-203261271 / 1000000000) (-20326127 / 100000000) (Real.log (163213 / 200000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (61545793 / 500000000) ≤ -Real.log (250000 / 282747) ∧
    -Real.log (250000 / 282747) ≤ (123091587 / 1000000000) := by
  have h := checkLog_sound (w := (32747 / 532747)) (n := 12)
    (lo := (61545793 / 500000000)) (hi := (123091587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((282747 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(282747 / 250000) = 1/(250000 / 282747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (61545793 / 500000000) (123091587 / 1000000000) (Real.log (282747 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (282747 / 250000) = -Real.log (250000 / 282747) := by
    rw [show ((282747 / 250000) : ℝ) = ((250000 / 282747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (17549793 / 125000000) ≤ -Real.log (217253 / 250000) ∧
    -Real.log (217253 / 250000) ≤ (28079669 / 200000000) := by
  have h := checkLog_sound (w := (32747 / 467253)) (n := 12)
    (lo := (17549793 / 125000000)) (hi := (28079669 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 217253) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 217253) = 1/(217253 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-28079669 / 200000000) (-17549793 / 125000000) (Real.log (217253 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (61680613 / 500000000) ≤ -Real.log (1000000 / 1131293) ∧
    -Real.log (1000000 / 1131293) ≤ (123361227 / 1000000000) := by
  have h := checkLog_sound (w := (131293 / 2131293)) (n := 12)
    (lo := (61680613 / 500000000)) (hi := (123361227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1131293 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1131293 / 1000000) = 1/(1000000 / 1131293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (61680613 / 500000000) (123361227 / 1000000000) (Real.log (1131293 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1131293 / 1000000) = -Real.log (1000000 / 1131293) := by
    rw [show ((1131293 / 1000000) : ℝ) = ((1000000 / 1131293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (140749379 / 1000000000) ≤ -Real.log (868707 / 1000000) ∧
    -Real.log (868707 / 1000000) ≤ (7037469 / 50000000) := by
  have h := checkLog_sound (w := (131293 / 1868707)) (n := 12)
    (lo := (140749379 / 1000000000)) (hi := (7037469 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 868707) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 868707) = 1/(868707 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-7037469 / 50000000) (-140749379 / 1000000000) (Real.log (868707 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (21184809 / 40000000) ≤ -Real.log (500000000000 / 849143610013) ∧
    -Real.log (500000000000 / 849143610013) ≤ (264810113 / 500000000) := by
  have h := checkLog_sound (w := (349143610013 / 1349143610013)) (n := 12)
    (lo := (21184809 / 40000000)) (hi := (264810113 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((849143610013 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(849143610013 / 500000000000) = 1/(500000000000 / 849143610013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (21184809 / 40000000) (264810113 / 500000000) (Real.log (849143610013 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (849143610013 / 500000000000) = -Real.log (500000000000 / 849143610013) := by
    rw [show ((849143610013 / 500000000000) : ℝ) = ((500000000000 / 849143610013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (26543821 / 50000000) ≤ -Real.log (100000000000 / 170042194093) ∧
    -Real.log (100000000000 / 170042194093) ≤ (530876421 / 1000000000) := by
  have h := checkLog_sound (w := (70042194093 / 270042194093)) (n := 12)
    (lo := (26543821 / 50000000)) (hi := (530876421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((170042194093 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(170042194093 / 100000000000) = 1/(100000000000 / 170042194093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (26543821 / 50000000) (530876421 / 1000000000) (Real.log (170042194093 / 100000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (170042194093 / 100000000000) = -Real.log (100000000000 / 170042194093) := by
    rw [show ((170042194093 / 100000000000) : ℝ) = ((100000000000 / 170042194093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (371237631 / 1000000000) ≤ -Real.log (500000000000 / 724763743073) ∧
    -Real.log (500000000000 / 724763743073) ≤ (1450147 / 3906250) := by
  have h := checkLog_sound (w := (224763743073 / 1224763743073)) (n := 12)
    (lo := (371237631 / 1000000000)) (hi := (1450147 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((724763743073 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(724763743073 / 500000000000) = 1/(500000000000 / 724763743073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (371237631 / 1000000000) (1450147 / 3906250) (Real.log (724763743073 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (724763743073 / 500000000000) = -Real.log (500000000000 / 724763743073) := by
    rw [show ((724763743073 / 500000000000) : ℝ) = ((500000000000 / 724763743073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (186052453 / 500000000) ≤ -Real.log (10000000000 / 14507851703) ∧
    -Real.log (10000000000 / 14507851703) ≤ (372104907 / 1000000000) := by
  have h := checkLog_sound (w := (4507851703 / 24507851703)) (n := 12)
    (lo := (186052453 / 500000000)) (hi := (372104907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14507851703 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14507851703 / 10000000000) = 1/(10000000000 / 14507851703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (186052453 / 500000000) (372104907 / 1000000000) (Real.log (14507851703 / 10000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (14507851703 / 10000000000) = -Real.log (10000000000 / 14507851703) := by
    rw [show ((14507851703 / 10000000000) : ℝ) = ((10000000000 / 14507851703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (263489931 / 1000000000) ≤ -Real.log (500000000000 / 650732095759) ∧
    -Real.log (500000000000 / 650732095759) ≤ (65872483 / 250000000) := by
  have h := checkLog_sound (w := (150732095759 / 1150732095759)) (n := 12)
    (lo := (263489931 / 1000000000)) (hi := (65872483 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((650732095759 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(650732095759 / 500000000000) = 1/(500000000000 / 650732095759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (263489931 / 1000000000) (65872483 / 250000000) (Real.log (650732095759 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (650732095759 / 500000000000) = -Real.log (500000000000 / 650732095759) := by
    rw [show ((650732095759 / 500000000000) : ℝ) = ((500000000000 / 650732095759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (132055303 / 500000000) ≤ -Real.log (125000000000 / 162784028447) ∧
    -Real.log (125000000000 / 162784028447) ≤ (264110607 / 1000000000) := by
  have h := checkLog_sound (w := (37784028447 / 287784028447)) (n := 12)
    (lo := (132055303 / 500000000)) (hi := (264110607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((162784028447 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(162784028447 / 125000000000) = 1/(125000000000 / 162784028447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (132055303 / 500000000) (264110607 / 1000000000) (Real.log (162784028447 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (162784028447 / 125000000000) = -Real.log (125000000000 / 162784028447) := by
    rw [show ((162784028447 / 125000000000) : ℝ) = ((125000000000 / 162784028447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (17388153 / 1000000000) ≤ -Real.log (982762148151 / 1000000000000) ∧
    -Real.log (982762148151 / 1000000000000) ≤ (8694077 / 500000000) := by
  have h := checkLog_sound (w := (17237851849 / 1982762148151)) (n := 12)
    (lo := (17388153 / 1000000000)) (hi := (8694077 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 982762148151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 982762148151) = 1/(982762148151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-8694077 / 500000000) (-17388153 / 1000000000) (Real.log (982762148151 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (17306757 / 1000000000) ≤ -Real.log (61427633991 / 62500000000) ∧
    -Real.log (61427633991 / 62500000000) ≤ (8653379 / 500000000) := by
  have h := checkLog_sound (w := (1072366009 / 123927633991)) (n := 12)
    (lo := (17306757 / 1000000000)) (hi := (8653379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61427633991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61427633991) = 1/(61427633991 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-8653379 / 500000000) (-17306757 / 1000000000) (Real.log (61427633991 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell015

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell016Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell016
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

theorem reflection_log_1_neg : (115540359 / 500000000) ≤ -Real.log (5120 / 6451) ∧
    -Real.log (5120 / 6451) ≤ (231080719 / 1000000000) := by
  have h := checkLog_sound (w := (1331 / 11571)) (n := 12)
    (lo := (115540359 / 500000000)) (hi := (231080719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6451 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6451 / 5120) = 1/(5120 / 6451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (115540359 / 500000000) (231080719 / 1000000000) (Real.log (6451 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6451 / 5120) = -Real.log (5120 / 6451) := by
    rw [show ((6451 / 5120) : ℝ) = ((5120 / 6451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (301052307 / 1000000000) ≤ -Real.log (3789 / 5120) ∧
    -Real.log (3789 / 5120) ≤ (75263077 / 250000000) := by
  have h := checkLog_sound (w := (1331 / 8909)) (n := 12)
    (lo := (301052307 / 1000000000)) (hi := (75263077 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3789) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3789) = 1/(3789 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-75263077 / 250000000) (-301052307 / 1000000000) (Real.log (3789 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (115307783 / 500000000) ≤ -Real.log (320 / 403) ∧
    -Real.log (320 / 403) ≤ (230615567 / 1000000000) := by
  have h := checkLog_sound (w := (83 / 723)) (n := 12)
    (lo := (115307783 / 500000000)) (hi := (230615567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((403 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(403 / 320) = 1/(320 / 403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (115307783 / 500000000) (230615567 / 1000000000) (Real.log (403 / 320)) := by
  have h := reflection_log_3_neg
  have he : Real.log (403 / 320) = -Real.log (320 / 403) := by
    rw [show ((403 / 320) : ℝ) = ((320 / 403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (150130427 / 500000000) ≤ -Real.log (237 / 320) ∧
    -Real.log (237 / 320) ≤ (60052171 / 200000000) := by
  have h := checkLog_sound (w := (83 / 557)) (n := 12)
    (lo := (150130427 / 500000000)) (hi := (60052171 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 237) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 237) = 1/(237 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-60052171 / 200000000) (-150130427 / 500000000) (Real.log (237 / 320)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (168842791 / 1000000000) ≤ -Real.log (500000 / 591967) ∧
    -Real.log (500000 / 591967) ≤ (21105349 / 125000000) := by
  have h := checkLog_sound (w := (91967 / 1091967)) (n := 12)
    (lo := (168842791 / 1000000000)) (hi := (21105349 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591967 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(591967 / 500000) = 1/(500000 / 591967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (168842791 / 1000000000) (21105349 / 125000000) (Real.log (591967 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (591967 / 500000) = -Real.log (500000 / 591967) := by
    rw [show ((591967 / 500000) : ℝ) = ((500000 / 591967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (50815011 / 250000000) ≤ -Real.log (408033 / 500000) ∧
    -Real.log (408033 / 500000) ≤ (40652009 / 200000000) := by
  have h := checkLog_sound (w := (91967 / 908033)) (n := 12)
    (lo := (50815011 / 250000000)) (hi := (40652009 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 408033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 408033) = 1/(408033 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-40652009 / 200000000) (-50815011 / 250000000) (Real.log (408033 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (169196633 / 1000000000) ≤ -Real.log (1000000 / 1184353) ∧
    -Real.log (1000000 / 1184353) ≤ (84598317 / 500000000) := by
  have h := checkLog_sound (w := (184353 / 2184353)) (n := 12)
    (lo := (169196633 / 1000000000)) (hi := (84598317 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1184353 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1184353 / 1000000) = 1/(1000000 / 1184353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (169196633 / 1000000000) (84598317 / 500000000) (Real.log (1184353 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1184353 / 1000000) = -Real.log (1000000 / 1184353) := by
    rw [show ((1184353 / 1000000) : ℝ) = ((1000000 / 1184353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (40754723 / 200000000) ≤ -Real.log (815647 / 1000000) ∧
    -Real.log (815647 / 1000000) ≤ (12735851 / 62500000) := by
  have h := checkLog_sound (w := (184353 / 1815647)) (n := 12)
    (lo := (40754723 / 200000000)) (hi := (12735851 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 815647) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 815647) = 1/(815647 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-12735851 / 62500000) (-40754723 / 200000000) (Real.log (815647 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (61680171 / 500000000) ≤ -Real.log (250000 / 282823) ∧
    -Real.log (250000 / 282823) ≤ (123360343 / 1000000000) := by
  have h := checkLog_sound (w := (32823 / 532823)) (n := 12)
    (lo := (61680171 / 500000000)) (hi := (123360343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((282823 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(282823 / 250000) = 1/(250000 / 282823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (61680171 / 500000000) (123360343 / 1000000000) (Real.log (282823 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (282823 / 250000) = -Real.log (250000 / 282823) := by
    rw [show ((282823 / 250000) : ℝ) = ((250000 / 282823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (35187057 / 250000000) ≤ -Real.log (217177 / 250000) ∧
    -Real.log (217177 / 250000) ≤ (140748229 / 1000000000) := by
  have h := checkLog_sound (w := (32823 / 467177)) (n := 12)
    (lo := (35187057 / 250000000)) (hi := (140748229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 217177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 217177) = 1/(217177 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-140748229 / 1000000000) (-35187057 / 250000000) (Real.log (217177 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (123629909 / 1000000000) ≤ -Real.log (1000000 / 1131597) ∧
    -Real.log (1000000 / 1131597) ≤ (12362991 / 100000000) := by
  have h := checkLog_sound (w := (131597 / 2131597)) (n := 12)
    (lo := (123629909 / 1000000000)) (hi := (12362991 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1131597 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1131597 / 1000000) = 1/(1000000 / 1131597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (123629909 / 1000000000) (12362991 / 100000000) (Real.log (1131597 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1131597 / 1000000) = -Real.log (1000000 / 1131597) := by
    rw [show ((1131597 / 1000000) : ℝ) = ((1000000 / 1131597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (70549693 / 500000000) ≤ -Real.log (868403 / 1000000) ∧
    -Real.log (868403 / 1000000) ≤ (141099387 / 1000000000) := by
  have h := checkLog_sound (w := (131597 / 1868403)) (n := 12)
    (lo := (70549693 / 500000000)) (hi := (141099387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 868403) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 868403) = 1/(868403 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-141099387 / 1000000000) (-70549693 / 500000000) (Real.log (868403 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (26543821 / 50000000) ≤ -Real.log (15625000000 / 26569092827) ∧
    -Real.log (15625000000 / 26569092827) ≤ (530876421 / 1000000000) := by
  have h := checkLog_sound (w := (10944092827 / 42194092827)) (n := 12)
    (lo := (26543821 / 50000000)) (hi := (530876421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26569092827 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(26569092827 / 15625000000) = 1/(15625000000 / 26569092827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (26543821 / 50000000) (530876421 / 1000000000) (Real.log (26569092827 / 15625000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (26569092827 / 15625000000) = -Real.log (15625000000 / 26569092827) := by
    rw [show ((26569092827 / 15625000000) : ℝ) = ((15625000000 / 26569092827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (21285321 / 40000000) ≤ -Real.log (250000000000 / 425640010557) ∧
    -Real.log (250000000000 / 425640010557) ≤ (266066513 / 500000000) := by
  have h := checkLog_sound (w := (175640010557 / 675640010557)) (n := 12)
    (lo := (21285321 / 40000000)) (hi := (266066513 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((425640010557 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(425640010557 / 250000000000) = 1/(250000000000 / 425640010557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (21285321 / 40000000) (266066513 / 500000000) (Real.log (425640010557 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (425640010557 / 250000000000) = -Real.log (250000000000 / 425640010557) := by
    rw [show ((425640010557 / 250000000000) : ℝ) = ((250000000000 / 425640010557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (93025709 / 250000000) ≤ -Real.log (125000000000 / 181347770891) ∧
    -Real.log (125000000000 / 181347770891) ≤ (372102837 / 1000000000) := by
  have h := checkLog_sound (w := (56347770891 / 306347770891)) (n := 12)
    (lo := (93025709 / 250000000)) (hi := (372102837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((181347770891 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(181347770891 / 125000000000) = 1/(125000000000 / 181347770891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (93025709 / 250000000) (372102837 / 1000000000) (Real.log (181347770891 / 125000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (181347770891 / 125000000000) = -Real.log (125000000000 / 181347770891) := by
    rw [show ((181347770891 / 125000000000) : ℝ) = ((125000000000 / 181347770891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (372970249 / 1000000000) ≤ -Real.log (250000000000 / 363010285087) ∧
    -Real.log (250000000000 / 363010285087) ≤ (1491881 / 4000000) := by
  have h := checkLog_sound (w := (113010285087 / 613010285087)) (n := 12)
    (lo := (372970249 / 1000000000)) (hi := (1491881 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((363010285087 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(363010285087 / 250000000000) = 1/(250000000000 / 363010285087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (372970249 / 1000000000) (1491881 / 4000000) (Real.log (363010285087 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (363010285087 / 250000000000) = -Real.log (250000000000 / 363010285087) := by
    rw [show ((363010285087 / 250000000000) : ℝ) = ((250000000000 / 363010285087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (264108571 / 1000000000) ≤ -Real.log (250000000000 / 325567394337) ∧
    -Real.log (250000000000 / 325567394337) ≤ (66027143 / 250000000) := by
  have h := checkLog_sound (w := (75567394337 / 575567394337)) (n := 12)
    (lo := (264108571 / 1000000000)) (hi := (66027143 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((325567394337 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(325567394337 / 250000000000) = 1/(250000000000 / 325567394337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (264108571 / 1000000000) (66027143 / 250000000) (Real.log (325567394337 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (325567394337 / 250000000000) = -Real.log (250000000000 / 325567394337) := by
    rw [show ((325567394337 / 250000000000) : ℝ) = ((250000000000 / 325567394337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (52945859 / 200000000) ≤ -Real.log (500000000000 / 651539089571) ∧
    -Real.log (500000000000 / 651539089571) ≤ (16545581 / 62500000) := by
  have h := checkLog_sound (w := (151539089571 / 1151539089571)) (n := 12)
    (lo := (52945859 / 200000000)) (hi := (16545581 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((651539089571 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(651539089571 / 500000000000) = 1/(500000000000 / 651539089571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (52945859 / 200000000) (16545581 / 62500000) (Real.log (651539089571 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (651539089571 / 500000000000) = -Real.log (500000000000 / 651539089571) := by
    rw [show ((651539089571 / 500000000000) : ℝ) = ((500000000000 / 651539089571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (17469477 / 1000000000) ≤ -Real.log (982682229591 / 1000000000000) ∧
    -Real.log (982682229591 / 1000000000000) ≤ (8734739 / 500000000) := by
  have h := checkLog_sound (w := (17317770409 / 1982682229591)) (n := 12)
    (lo := (17469477 / 1000000000)) (hi := (8734739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 982682229591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 982682229591) = 1/(982682229591 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-8734739 / 500000000) (-17469477 / 1000000000) (Real.log (982682229591 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (8693943 / 500000000) ≤ -Real.log (61422650671 / 62500000000) ∧
    -Real.log (61422650671 / 62500000000) ≤ (17387887 / 1000000000) := by
  have h := checkLog_sound (w := (1077349329 / 123922650671)) (n := 12)
    (lo := (8693943 / 500000000)) (hi := (17387887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61422650671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61422650671) = 1/(61422650671 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-17387887 / 1000000000) (-8693943 / 500000000) (Real.log (61422650671 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell016

end


