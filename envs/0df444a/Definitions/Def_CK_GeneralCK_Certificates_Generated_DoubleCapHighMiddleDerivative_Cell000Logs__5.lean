-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell000Logs__5
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell000Logs__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T17:27:42.840723+00:00
-- url     : https://prove2.me/theorems/ae0d2fd0-8156-428b-b690-8a8fa7e234fe
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell000Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell001…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell000Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell001Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell002Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell003Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell004Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell000Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell001Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell002Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell003Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell004Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell000Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell001Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell002Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell003Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell004Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell000Logs (+4 modules: GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell001Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell002Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell003Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell004Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell000Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell000
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

theorem reflection_log_1_neg : (223612191 / 1000000000) ≤ -Real.log (5120 / 6403) ∧
    -Real.log (5120 / 6403) ≤ (6987881 / 31250000) := by
  have h := checkLog_sound (w := (1283 / 11523)) (n := 12)
    (lo := (223612191 / 1000000000)) (hi := (6987881 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6403 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6403 / 5120) = 1/(5120 / 6403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (223612191 / 1000000000) (6987881 / 31250000) (Real.log (6403 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6403 / 5120) = -Real.log (5120 / 6403) := by
    rw [show ((6403 / 5120) : ℝ) = ((5120 / 6403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (288463627 / 1000000000) ≤ -Real.log (3837 / 5120) ∧
    -Real.log (3837 / 5120) ≤ (72115907 / 250000000) := by
  have h := checkLog_sound (w := (1283 / 8957)) (n := 12)
    (lo := (288463627 / 1000000000)) (hi := (72115907 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3837) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3837) = 1/(3837 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-72115907 / 250000000) (-288463627 / 1000000000) (Real.log (3837 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (223143551 / 1000000000) ≤ -Real.log (4 / 5) ∧
    -Real.log (4 / 5) ≤ (1743309 / 7812500) := by
  have h := checkLog_sound (w := (1 / 9)) (n := 12)
    (lo := (223143551 / 1000000000)) (hi := (1743309 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 4) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5 / 4) = 1/(4 / 5) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (223143551 / 1000000000) (1743309 / 7812500) (Real.log (5 / 4)) := by
  have h := reflection_log_3_neg
  have he : Real.log (5 / 4) = -Real.log (4 / 5) := by
    rw [show ((5 / 4) : ℝ) = ((4 / 5) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (35960259 / 125000000) ≤ -Real.log (3 / 4) ∧
    -Real.log (3 / 4) ≤ (287682073 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 7)) (n := 12)
    (lo := (35960259 / 125000000)) (hi := (287682073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4 / 3) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4 / 3) = 1/(3 / 4) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-287682073 / 1000000000) (-35960259 / 125000000) (Real.log (3 / 4)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (4079509 / 25000000) ≤ -Real.log (1000000 / 1177249) ∧
    -Real.log (1000000 / 1177249) ≤ (163180361 / 1000000000) := by
  have h := checkLog_sound (w := (177249 / 2177249)) (n := 12)
    (lo := (4079509 / 25000000)) (hi := (163180361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1177249 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1177249 / 1000000) = 1/(1000000 / 1177249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (4079509 / 25000000) (163180361 / 1000000000) (Real.log (1177249 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1177249 / 1000000) = -Real.log (1000000 / 1177249) := by
    rw [show ((1177249 / 1000000) : ℝ) = ((1000000 / 1177249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (7804067 / 40000000) ≤ -Real.log (822751 / 1000000) ∧
    -Real.log (822751 / 1000000) ≤ (48775419 / 250000000) := by
  have h := checkLog_sound (w := (177249 / 1822751)) (n := 12)
    (lo := (7804067 / 40000000)) (hi := (48775419 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 822751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 822751) = 1/(822751 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-48775419 / 250000000) (-7804067 / 40000000) (Real.log (822751 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (163536211 / 1000000000) ≤ -Real.log (250000 / 294417) ∧
    -Real.log (250000 / 294417) ≤ (40884053 / 250000000) := by
  have h := checkLog_sound (w := (44417 / 544417)) (n := 12)
    (lo := (163536211 / 1000000000)) (hi := (40884053 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294417 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(294417 / 250000) = 1/(250000 / 294417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (163536211 / 1000000000) (40884053 / 250000000) (Real.log (294417 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (294417 / 250000) = -Real.log (250000 / 294417) := by
    rw [show ((294417 / 250000) : ℝ) = ((250000 / 294417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3056423 / 15625000) ≤ -Real.log (205583 / 250000) ∧
    -Real.log (205583 / 250000) ≤ (195611073 / 1000000000) := by
  have h := checkLog_sound (w := (44417 / 455583)) (n := 12)
    (lo := (3056423 / 15625000)) (hi := (195611073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 205583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 205583) = 1/(205583 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-195611073 / 1000000000) (-3056423 / 15625000) (Real.log (205583 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (59528889 / 500000000) ≤ -Real.log (200000 / 225287) ∧
    -Real.log (200000 / 225287) ≤ (119057779 / 1000000000) := by
  have h := checkLog_sound (w := (25287 / 425287)) (n := 12)
    (lo := (59528889 / 500000000)) (hi := (119057779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((225287 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(225287 / 200000) = 1/(200000 / 225287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (59528889 / 500000000) (119057779 / 1000000000) (Real.log (225287 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (225287 / 200000) = -Real.log (200000 / 225287) := by
    rw [show ((225287 / 200000) : ℝ) = ((200000 / 225287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (67586369 / 500000000) ≤ -Real.log (174713 / 200000) ∧
    -Real.log (174713 / 200000) ≤ (135172739 / 1000000000) := by
  have h := checkLog_sound (w := (25287 / 374713)) (n := 12)
    (lo := (67586369 / 500000000)) (hi := (135172739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 174713) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 174713) = 1/(174713 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-135172739 / 1000000000) (-67586369 / 500000000) (Real.log (174713 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (119327619 / 1000000000) ≤ -Real.log (1000000 / 1126739) ∧
    -Real.log (1000000 / 1126739) ≤ (5966381 / 50000000) := by
  have h := checkLog_sound (w := (126739 / 2126739)) (n := 12)
    (lo := (119327619 / 1000000000)) (hi := (5966381 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1126739 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1126739 / 1000000) = 1/(1000000 / 1126739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (119327619 / 1000000000) (5966381 / 50000000) (Real.log (1126739 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1126739 / 1000000) = -Real.log (1000000 / 1126739) := by
    rw [show ((1126739 / 1000000) : ℝ) = ((1000000 / 1126739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (67760399 / 500000000) ≤ -Real.log (873261 / 1000000) ∧
    -Real.log (873261 / 1000000) ≤ (135520799 / 1000000000) := by
  have h := checkLog_sound (w := (126739 / 1873261)) (n := 12)
    (lo := (67760399 / 500000000)) (hi := (135520799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 873261) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 873261) = 1/(873261 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-135520799 / 1000000000) (-67760399 / 500000000) (Real.log (873261 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (510825623 / 1000000000) ≤ -Real.log (500000000000 / 833333333333) ∧
    -Real.log (500000000000 / 833333333333) ≤ (63853203 / 125000000) := by
  have h := checkLog_sound (w := (333333333333 / 1333333333333)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((833333333333 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(833333333333 / 500000000000) = 1/(500000000000 / 833333333333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (510825623 / 1000000000) (63853203 / 125000000) (Real.log (833333333333 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (833333333333 / 500000000000) = -Real.log (500000000000 / 833333333333) := by
    rw [show ((833333333333 / 500000000000) : ℝ) = ((500000000000 / 833333333333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (512075819 / 1000000000) ≤ -Real.log (500000000000 / 834375814439) ∧
    -Real.log (500000000000 / 834375814439) ≤ (25603791 / 50000000) := by
  have h := checkLog_sound (w := (334375814439 / 1334375814439)) (n := 12)
    (lo := (512075819 / 1000000000)) (hi := (25603791 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((834375814439 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(834375814439 / 500000000000) = 1/(500000000000 / 834375814439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (512075819 / 1000000000) (25603791 / 50000000) (Real.log (834375814439 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (834375814439 / 500000000000) = -Real.log (500000000000 / 834375814439) := by
    rw [show ((834375814439 / 500000000000) : ℝ) = ((500000000000 / 834375814439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (89570509 / 250000000) ≤ -Real.log (100000000000 / 143086912079) ∧
    -Real.log (100000000000 / 143086912079) ≤ (358282037 / 1000000000) := by
  have h := checkLog_sound (w := (43086912079 / 243086912079)) (n := 12)
    (lo := (89570509 / 250000000)) (hi := (358282037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((143086912079 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(143086912079 / 100000000000) = 1/(100000000000 / 143086912079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (89570509 / 250000000) (358282037 / 1000000000) (Real.log (143086912079 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (143086912079 / 100000000000) = -Real.log (100000000000 / 143086912079) := by
    rw [show ((143086912079 / 100000000000) : ℝ) = ((100000000000 / 143086912079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (89786821 / 250000000) ≤ -Real.log (250000000000 / 358026928297) ∧
    -Real.log (250000000000 / 358026928297) ≤ (71829457 / 200000000) := by
  have h := checkLog_sound (w := (108026928297 / 608026928297)) (n := 12)
    (lo := (89786821 / 250000000)) (hi := (71829457 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((358026928297 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(358026928297 / 250000000000) = 1/(250000000000 / 358026928297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (89786821 / 250000000) (71829457 / 200000000) (Real.log (358026928297 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (358026928297 / 250000000000) = -Real.log (250000000000 / 358026928297) := by
    rw [show ((358026928297 / 250000000000) : ℝ) = ((250000000000 / 358026928297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (254230517 / 1000000000) ≤ -Real.log (500000000000 / 644734507449) ∧
    -Real.log (500000000000 / 644734507449) ≤ (127115259 / 500000000) := by
  have h := checkLog_sound (w := (144734507449 / 1144734507449)) (n := 12)
    (lo := (254230517 / 1000000000)) (hi := (127115259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((644734507449 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(644734507449 / 500000000000) = 1/(500000000000 / 644734507449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (254230517 / 1000000000) (127115259 / 500000000) (Real.log (644734507449 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (644734507449 / 500000000000) = -Real.log (500000000000 / 644734507449) := by
    rw [show ((644734507449 / 500000000000) : ℝ) = ((500000000000 / 644734507449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (127424209 / 500000000) ≤ -Real.log (250000000000 / 322566506463) ∧
    -Real.log (250000000000 / 322566506463) ≤ (254848419 / 1000000000) := by
  have h := checkLog_sound (w := (72566506463 / 572566506463)) (n := 12)
    (lo := (127424209 / 500000000)) (hi := (254848419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((322566506463 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(322566506463 / 250000000000) = 1/(250000000000 / 322566506463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (127424209 / 500000000) (254848419 / 1000000000) (Real.log (322566506463 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (322566506463 / 250000000000) = -Real.log (250000000000 / 322566506463) := by
    rw [show ((322566506463 / 250000000000) : ℝ) = ((250000000000 / 322566506463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (8096589 / 500000000) ≤ -Real.log (983937225879 / 1000000000000) ∧
    -Real.log (983937225879 / 1000000000000) ≤ (16193179 / 1000000000) := by
  have h := checkLog_sound (w := (16062774121 / 1983937225879)) (n := 12)
    (lo := (8096589 / 500000000)) (hi := (16193179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 983937225879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 983937225879) = 1/(983937225879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-16193179 / 1000000000) (-8096589 / 500000000) (Real.log (983937225879 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (201437 / 12500000) ≤ -Real.log (39360567631 / 40000000000) ∧
    -Real.log (39360567631 / 40000000000) ≤ (16114961 / 1000000000) := by
  have h := checkLog_sound (w := (639432369 / 79360567631)) (n := 12)
    (lo := (201437 / 12500000)) (hi := (16114961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39360567631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39360567631) = 1/(39360567631 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-16114961 / 1000000000) (-201437 / 12500000) (Real.log (39360567631 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell000

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell001Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell001
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

theorem reflection_log_1_neg : (56020153 / 250000000) ≤ -Real.log (2560 / 3203) ∧
    -Real.log (2560 / 3203) ≤ (224080613 / 1000000000) := by
  have h := checkLog_sound (w := (643 / 5763)) (n := 12)
    (lo := (56020153 / 250000000)) (hi := (224080613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3203 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3203 / 2560) = 1/(2560 / 3203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (56020153 / 250000000) (224080613 / 1000000000) (Real.log (3203 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3203 / 2560) = -Real.log (2560 / 3203) := by
    rw [show ((3203 / 2560) : ℝ) = ((2560 / 3203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (144622897 / 500000000) ≤ -Real.log (1917 / 2560) ∧
    -Real.log (1917 / 2560) ≤ (57849159 / 200000000) := by
  have h := checkLog_sound (w := (643 / 4477)) (n := 12)
    (lo := (144622897 / 500000000)) (hi := (57849159 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1917) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1917) = 1/(1917 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-57849159 / 200000000) (-144622897 / 500000000) (Real.log (1917 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (223612191 / 1000000000) ≤ -Real.log (5120 / 6403) ∧
    -Real.log (5120 / 6403) ≤ (6987881 / 31250000) := by
  have h := checkLog_sound (w := (1283 / 11523)) (n := 12)
    (lo := (223612191 / 1000000000)) (hi := (6987881 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6403 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6403 / 5120) = 1/(5120 / 6403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (223612191 / 1000000000) (6987881 / 31250000) (Real.log (6403 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6403 / 5120) = -Real.log (5120 / 6403) := by
    rw [show ((6403 / 5120) : ℝ) = ((5120 / 6403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (288463627 / 1000000000) ≤ -Real.log (3837 / 5120) ∧
    -Real.log (3837 / 5120) ≤ (72115907 / 250000000) := by
  have h := checkLog_sound (w := (1283 / 8957)) (n := 12)
    (lo := (288463627 / 1000000000)) (hi := (72115907 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3837) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3837) = 1/(3837 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-72115907 / 250000000) (-288463627 / 1000000000) (Real.log (3837 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (81767681 / 500000000) ≤ -Real.log (1000000 / 1177667) ∧
    -Real.log (1000000 / 1177667) ≤ (163535363 / 1000000000) := by
  have h := checkLog_sound (w := (177667 / 2177667)) (n := 12)
    (lo := (81767681 / 500000000)) (hi := (163535363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1177667 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1177667 / 1000000) = 1/(1000000 / 1177667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (81767681 / 500000000) (163535363 / 1000000000) (Real.log (1177667 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1177667 / 1000000) = -Real.log (1000000 / 1177667) := by
    rw [show ((1177667 / 1000000) : ℝ) = ((1000000 / 1177667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (764101 / 3906250) ≤ -Real.log (822333 / 1000000) ∧
    -Real.log (822333 / 1000000) ≤ (195609857 / 1000000000) := by
  have h := checkLog_sound (w := (177667 / 1822333)) (n := 12)
    (lo := (764101 / 3906250)) (hi := (195609857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 822333) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 822333) = 1/(822333 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-195609857 / 1000000000) (-764101 / 3906250) (Real.log (822333 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (81945119 / 500000000) ≤ -Real.log (200000 / 235617) ∧
    -Real.log (200000 / 235617) ≤ (163890239 / 1000000000) := by
  have h := checkLog_sound (w := (35617 / 435617)) (n := 12)
    (lo := (81945119 / 500000000)) (hi := (163890239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((235617 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(235617 / 200000) = 1/(200000 / 235617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (81945119 / 500000000) (163890239 / 1000000000) (Real.log (235617 / 200000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (235617 / 200000) = -Real.log (200000 / 235617) := by
    rw [show ((235617 / 200000) : ℝ) = ((200000 / 235617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (39223659 / 200000000) ≤ -Real.log (164383 / 200000) ∧
    -Real.log (164383 / 200000) ≤ (24514787 / 125000000) := by
  have h := checkLog_sound (w := (35617 / 364383)) (n := 12)
    (lo := (39223659 / 200000000)) (hi := (24514787 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 164383) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 164383) = 1/(164383 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-24514787 / 125000000) (-39223659 / 200000000) (Real.log (164383 / 200000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (29831683 / 250000000) ≤ -Real.log (500000 / 563369) ∧
    -Real.log (500000 / 563369) ≤ (119326733 / 1000000000) := by
  have h := checkLog_sound (w := (63369 / 1063369)) (n := 12)
    (lo := (29831683 / 250000000)) (hi := (119326733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((563369 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(563369 / 500000) = 1/(500000 / 563369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (29831683 / 250000000) (119326733 / 1000000000) (Real.log (563369 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (563369 / 500000) = -Real.log (500000 / 563369) := by
    rw [show ((563369 / 500000) : ℝ) = ((500000 / 563369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (135519653 / 1000000000) ≤ -Real.log (436631 / 500000) ∧
    -Real.log (436631 / 500000) ≤ (67759827 / 500000000) := by
  have h := checkLog_sound (w := (63369 / 936631)) (n := 12)
    (lo := (135519653 / 1000000000)) (hi := (67759827 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 436631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 436631) = 1/(436631 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-67759827 / 500000000) (-135519653 / 1000000000) (Real.log (436631 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (119596501 / 1000000000) ≤ -Real.log (500000 / 563521) ∧
    -Real.log (500000 / 563521) ≤ (59798251 / 500000000) := by
  have h := checkLog_sound (w := (63521 / 1063521)) (n := 12)
    (lo := (119596501 / 1000000000)) (hi := (59798251 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((563521 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(563521 / 500000) = 1/(500000 / 563521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (119596501 / 1000000000) (59798251 / 500000000) (Real.log (563521 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (563521 / 500000) = -Real.log (500000 / 563521) := by
    rw [show ((563521 / 500000) : ℝ) = ((500000 / 563521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (67933917 / 500000000) ≤ -Real.log (436479 / 500000) ∧
    -Real.log (436479 / 500000) ≤ (27173567 / 200000000) := by
  have h := checkLog_sound (w := (63521 / 936479)) (n := 12)
    (lo := (67933917 / 500000000)) (hi := (27173567 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 436479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 436479) = 1/(436479 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-27173567 / 200000000) (-67933917 / 500000000) (Real.log (436479 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (512075819 / 1000000000) ≤ -Real.log (250000000000 / 417187907219) ∧
    -Real.log (250000000000 / 417187907219) ≤ (25603791 / 50000000) := by
  have h := checkLog_sound (w := (167187907219 / 667187907219)) (n := 12)
    (lo := (512075819 / 1000000000)) (hi := (25603791 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((417187907219 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(417187907219 / 250000000000) = 1/(250000000000 / 417187907219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (512075819 / 1000000000) (25603791 / 50000000) (Real.log (417187907219 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (417187907219 / 250000000000) = -Real.log (250000000000 / 417187907219) := by
    rw [show ((417187907219 / 250000000000) : ℝ) = ((250000000000 / 417187907219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (256663203 / 500000000) ≤ -Real.log (50000000000 / 83541992697) ∧
    -Real.log (50000000000 / 83541992697) ≤ (513326407 / 1000000000) := by
  have h := checkLog_sound (w := (33541992697 / 133541992697)) (n := 12)
    (lo := (256663203 / 500000000)) (hi := (513326407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((83541992697 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(83541992697 / 50000000000) = 1/(50000000000 / 83541992697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (256663203 / 500000000) (513326407 / 1000000000) (Real.log (83541992697 / 50000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (83541992697 / 50000000000) = -Real.log (50000000000 / 83541992697) := by
    rw [show ((83541992697 / 50000000000) : ℝ) = ((50000000000 / 83541992697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (359145219 / 1000000000) ≤ -Real.log (31250000000 / 44753273613) ∧
    -Real.log (31250000000 / 44753273613) ≤ (17957261 / 50000000) := by
  have h := checkLog_sound (w := (13503273613 / 76003273613)) (n := 12)
    (lo := (359145219 / 1000000000)) (hi := (17957261 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44753273613 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(44753273613 / 31250000000) = 1/(31250000000 / 44753273613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (359145219 / 1000000000) (17957261 / 50000000) (Real.log (44753273613 / 31250000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (44753273613 / 31250000000) = -Real.log (31250000000 / 44753273613) := by
    rw [show ((44753273613 / 31250000000) : ℝ) = ((31250000000 / 44753273613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (180004267 / 500000000) ≤ -Real.log (250000000000 / 358335411813) ∧
    -Real.log (250000000000 / 358335411813) ≤ (72001707 / 200000000) := by
  have h := checkLog_sound (w := (108335411813 / 608335411813)) (n := 12)
    (lo := (180004267 / 500000000)) (hi := (72001707 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((358335411813 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(358335411813 / 250000000000) = 1/(250000000000 / 358335411813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (180004267 / 500000000) (72001707 / 200000000) (Real.log (358335411813 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (358335411813 / 250000000000) = -Real.log (250000000000 / 358335411813) := by
    rw [show ((358335411813 / 250000000000) : ℝ) = ((250000000000 / 358335411813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (127423193 / 500000000) ≤ -Real.log (500000000000 / 645131701597) ∧
    -Real.log (500000000000 / 645131701597) ≤ (254846387 / 1000000000) := by
  have h := checkLog_sound (w := (145131701597 / 1145131701597)) (n := 12)
    (lo := (127423193 / 500000000)) (hi := (254846387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((645131701597 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(645131701597 / 500000000000) = 1/(500000000000 / 645131701597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (127423193 / 500000000) (254846387 / 1000000000) (Real.log (645131701597 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (645131701597 / 500000000000) = -Real.log (500000000000 / 645131701597) := by
    rw [show ((645131701597 / 500000000000) : ℝ) = ((500000000000 / 645131701597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (51092867 / 200000000) ≤ -Real.log (488281250 / 630400863) ∧
    -Real.log (488281250 / 630400863) ≤ (15966521 / 62500000) := by
  have h := checkLog_sound (w := (142119613 / 1118682113)) (n := 12)
    (lo := (51092867 / 200000000)) (hi := (15966521 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((630400863 / 488281250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(630400863 / 488281250) = 1/(488281250 / 630400863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (51092867 / 200000000) (15966521 / 62500000) (Real.log (630400863 / 488281250)) := by
  have h := reflection_log_18_neg
  have he : Real.log (630400863 / 488281250) = -Real.log (488281250 / 630400863) := by
    rw [show ((630400863 / 488281250) : ℝ) = ((488281250 / 630400863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4067833 / 250000000) ≤ -Real.log (245965082559 / 250000000000) ∧
    -Real.log (245965082559 / 250000000000) ≤ (16271333 / 1000000000) := by
  have h := checkLog_sound (w := (4034917441 / 495965082559)) (n := 12)
    (lo := (4067833 / 250000000)) (hi := (16271333 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245965082559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245965082559) = 1/(245965082559 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-16271333 / 1000000000) (-4067833 / 250000000) (Real.log (245965082559 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (16192921 / 1000000000) ≤ -Real.log (245984369839 / 250000000000) ∧
    -Real.log (245984369839 / 250000000000) ≤ (8096461 / 500000000) := by
  have h := checkLog_sound (w := (4015630161 / 495984369839)) (n := 12)
    (lo := (16192921 / 1000000000)) (hi := (8096461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245984369839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245984369839) = 1/(245984369839 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-8096461 / 500000000) (-16192921 / 1000000000) (Real.log (245984369839 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell001

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell002Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell002
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

theorem reflection_log_1_neg : (224548813 / 1000000000) ≤ -Real.log (5120 / 6409) ∧
    -Real.log (5120 / 6409) ≤ (112274407 / 500000000) := by
  have h := checkLog_sound (w := (1289 / 11529)) (n := 12)
    (lo := (224548813 / 1000000000)) (hi := (112274407 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6409 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6409 / 5120) = 1/(5120 / 6409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (224548813 / 1000000000) (112274407 / 500000000) (Real.log (6409 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6409 / 5120) = -Real.log (5120 / 6409) := by
    rw [show ((6409 / 5120) : ℝ) = ((5120 / 6409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (290028573 / 1000000000) ≤ -Real.log (3831 / 5120) ∧
    -Real.log (3831 / 5120) ≤ (145014287 / 500000000) := by
  have h := checkLog_sound (w := (1289 / 8951)) (n := 12)
    (lo := (290028573 / 1000000000)) (hi := (145014287 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3831) = 1/(3831 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-145014287 / 500000000) (-290028573 / 1000000000) (Real.log (3831 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (56020153 / 250000000) ≤ -Real.log (2560 / 3203) ∧
    -Real.log (2560 / 3203) ≤ (224080613 / 1000000000) := by
  have h := checkLog_sound (w := (643 / 5763)) (n := 12)
    (lo := (56020153 / 250000000)) (hi := (224080613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3203 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3203 / 2560) = 1/(2560 / 3203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (56020153 / 250000000) (224080613 / 1000000000) (Real.log (3203 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3203 / 2560) = -Real.log (2560 / 3203) := by
    rw [show ((3203 / 2560) : ℝ) = ((2560 / 3203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (144622897 / 500000000) ≤ -Real.log (1917 / 2560) ∧
    -Real.log (1917 / 2560) ≤ (57849159 / 200000000) := by
  have h := checkLog_sound (w := (643 / 4477)) (n := 12)
    (lo := (144622897 / 500000000)) (hi := (57849159 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1917) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1917) = 1/(1917 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-57849159 / 200000000) (-144622897 / 500000000) (Real.log (1917 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (163889389 / 1000000000) ≤ -Real.log (250000 / 294521) ∧
    -Real.log (250000 / 294521) ≤ (16388939 / 100000000) := by
  have h := checkLog_sound (w := (44521 / 544521)) (n := 12)
    (lo := (163889389 / 1000000000)) (hi := (16388939 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294521 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(294521 / 250000) = 1/(250000 / 294521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (163889389 / 1000000000) (16388939 / 100000000) (Real.log (294521 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (294521 / 250000) = -Real.log (250000 / 294521) := by
    rw [show ((294521 / 250000) : ℝ) = ((250000 / 294521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (98058539 / 500000000) ≤ -Real.log (205479 / 250000) ∧
    -Real.log (205479 / 250000) ≤ (196117079 / 1000000000) := by
  have h := checkLog_sound (w := (44521 / 455479)) (n := 12)
    (lo := (98058539 / 500000000)) (hi := (196117079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 205479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 205479) = 1/(205479 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-196117079 / 1000000000) (-98058539 / 500000000) (Real.log (205479 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (41061247 / 250000000) ≤ -Real.log (1000000 / 1178503) ∧
    -Real.log (1000000 / 1178503) ≤ (164244989 / 1000000000) := by
  have h := checkLog_sound (w := (178503 / 2178503)) (n := 12)
    (lo := (41061247 / 250000000)) (hi := (164244989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1178503 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1178503 / 1000000) = 1/(1000000 / 1178503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (41061247 / 250000000) (164244989 / 1000000000) (Real.log (1178503 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1178503 / 1000000) = -Real.log (1000000 / 1178503) := by
    rw [show ((1178503 / 1000000) : ℝ) = ((1000000 / 1178503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (196626993 / 1000000000) ≤ -Real.log (821497 / 1000000) ∧
    -Real.log (821497 / 1000000) ≤ (98313497 / 500000000) := by
  have h := checkLog_sound (w := (178503 / 1821497)) (n := 12)
    (lo := (196626993 / 1000000000)) (hi := (98313497 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 821497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 821497) = 1/(821497 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-98313497 / 500000000) (-196626993 / 1000000000) (Real.log (821497 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (59797807 / 500000000) ≤ -Real.log (1000000 / 1127041) ∧
    -Real.log (1000000 / 1127041) ≤ (23919123 / 200000000) := by
  have h := checkLog_sound (w := (127041 / 2127041)) (n := 12)
    (lo := (59797807 / 500000000)) (hi := (23919123 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1127041 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1127041 / 1000000) = 1/(1000000 / 1127041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (59797807 / 500000000) (23919123 / 200000000) (Real.log (1127041 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1127041 / 1000000) = -Real.log (1000000 / 1127041) := by
    rw [show ((1127041 / 1000000) : ℝ) = ((1000000 / 1127041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2122917 / 15625000) ≤ -Real.log (872959 / 1000000) ∧
    -Real.log (872959 / 1000000) ≤ (135866689 / 1000000000) := by
  have h := checkLog_sound (w := (127041 / 1872959)) (n := 12)
    (lo := (2122917 / 15625000)) (hi := (135866689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 872959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 872959) = 1/(872959 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-135866689 / 1000000000) (-2122917 / 15625000) (Real.log (872959 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (119866197 / 1000000000) ≤ -Real.log (500000 / 563673) ∧
    -Real.log (500000 / 563673) ≤ (59933099 / 500000000) := by
  have h := checkLog_sound (w := (63673 / 1063673)) (n := 12)
    (lo := (119866197 / 1000000000)) (hi := (59933099 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((563673 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(563673 / 500000) = 1/(500000 / 563673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (119866197 / 1000000000) (59933099 / 500000000) (Real.log (563673 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (563673 / 500000) = -Real.log (500000 / 563673) := by
    rw [show ((563673 / 500000) : ℝ) = ((500000 / 563673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (17027017 / 125000000) ≤ -Real.log (436327 / 500000) ∧
    -Real.log (436327 / 500000) ≤ (136216137 / 1000000000) := by
  have h := checkLog_sound (w := (63673 / 936327)) (n := 12)
    (lo := (17027017 / 125000000)) (hi := (136216137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 436327) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 436327) = 1/(436327 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-136216137 / 1000000000) (-17027017 / 125000000) (Real.log (436327 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (256663203 / 500000000) ≤ -Real.log (500000000000 / 835419926969) ∧
    -Real.log (500000000000 / 835419926969) ≤ (513326407 / 1000000000) := by
  have h := checkLog_sound (w := (335419926969 / 1335419926969)) (n := 12)
    (lo := (256663203 / 500000000)) (hi := (513326407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((835419926969 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(835419926969 / 500000000000) = 1/(500000000000 / 835419926969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (256663203 / 500000000) (513326407 / 1000000000) (Real.log (835419926969 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (835419926969 / 500000000000) = -Real.log (500000000000 / 835419926969) := by
    rw [show ((835419926969 / 500000000000) : ℝ) = ((500000000000 / 835419926969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (257288693 / 500000000) ≤ -Real.log (500000000000 / 836465674759) ∧
    -Real.log (500000000000 / 836465674759) ≤ (514577387 / 1000000000) := by
  have h := checkLog_sound (w := (336465674759 / 1336465674759)) (n := 12)
    (lo := (257288693 / 500000000)) (hi := (514577387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((836465674759 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(836465674759 / 500000000000) = 1/(500000000000 / 836465674759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (257288693 / 500000000) (514577387 / 1000000000) (Real.log (836465674759 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (836465674759 / 500000000000) = -Real.log (500000000000 / 836465674759) := by
    rw [show ((836465674759 / 500000000000) : ℝ) = ((500000000000 / 836465674759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (90001617 / 250000000) ≤ -Real.log (500000000000 / 716669343339) ∧
    -Real.log (500000000000 / 716669343339) ≤ (360006469 / 1000000000) := by
  have h := checkLog_sound (w := (216669343339 / 1216669343339)) (n := 12)
    (lo := (90001617 / 250000000)) (hi := (360006469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((716669343339 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(716669343339 / 500000000000) = 1/(500000000000 / 716669343339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (90001617 / 250000000) (360006469 / 1000000000) (Real.log (716669343339 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (716669343339 / 500000000000) = -Real.log (500000000000 / 716669343339) := by
    rw [show ((716669343339 / 500000000000) : ℝ) = ((500000000000 / 716669343339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (180435991 / 500000000) ≤ -Real.log (500000000000 / 717289898807) ∧
    -Real.log (500000000000 / 717289898807) ≤ (360871983 / 1000000000) := by
  have h := checkLog_sound (w := (217289898807 / 1217289898807)) (n := 12)
    (lo := (180435991 / 500000000)) (hi := (360871983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((717289898807 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(717289898807 / 500000000000) = 1/(500000000000 / 717289898807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (180435991 / 500000000) (360871983 / 1000000000) (Real.log (717289898807 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (717289898807 / 500000000000) = -Real.log (500000000000 / 717289898807) := by
    rw [show ((717289898807 / 500000000000) : ℝ) = ((500000000000 / 717289898807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (127731151 / 500000000) ≤ -Real.log (500000000000 / 645529171473) ∧
    -Real.log (500000000000 / 645529171473) ≤ (255462303 / 1000000000) := by
  have h := checkLog_sound (w := (145529171473 / 1145529171473)) (n := 12)
    (lo := (127731151 / 500000000)) (hi := (255462303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((645529171473 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(645529171473 / 500000000000) = 1/(500000000000 / 645529171473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (127731151 / 500000000) (255462303 / 1000000000) (Real.log (645529171473 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (645529171473 / 500000000000) = -Real.log (500000000000 / 645529171473) := by
    rw [show ((645529171473 / 500000000000) : ℝ) = ((500000000000 / 645529171473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (256082333 / 1000000000) ≤ -Real.log (125000000000 / 161482385917) ∧
    -Real.log (125000000000 / 161482385917) ≤ (128041167 / 500000000) := by
  have h := checkLog_sound (w := (36482385917 / 286482385917)) (n := 12)
    (lo := (256082333 / 1000000000)) (hi := (128041167 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161482385917 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(161482385917 / 125000000000) = 1/(125000000000 / 161482385917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (256082333 / 1000000000) (128041167 / 500000000) (Real.log (161482385917 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (161482385917 / 125000000000) = -Real.log (125000000000 / 161482385917) := by
    rw [show ((161482385917 / 125000000000) : ℝ) = ((125000000000 / 161482385917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (8174969 / 500000000) ≤ -Real.log (245945749071 / 250000000000) ∧
    -Real.log (245945749071 / 250000000000) ≤ (16349939 / 1000000000) := by
  have h := checkLog_sound (w := (4054250929 / 495945749071)) (n := 12)
    (lo := (8174969 / 500000000)) (hi := (16349939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245945749071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245945749071) = 1/(245945749071 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-16349939 / 1000000000) (-8174969 / 500000000) (Real.log (245945749071 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (8135537 / 500000000) ≤ -Real.log (983860584319 / 1000000000000) ∧
    -Real.log (983860584319 / 1000000000000) ≤ (650843 / 40000000) := by
  have h := checkLog_sound (w := (16139415681 / 1983860584319)) (n := 12)
    (lo := (8135537 / 500000000)) (hi := (650843 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 983860584319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 983860584319) = 1/(983860584319 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-650843 / 40000000) (-8135537 / 500000000) (Real.log (983860584319 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell002

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell003Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell003
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

theorem reflection_log_1_neg : (45003359 / 200000000) ≤ -Real.log (1280 / 1603) ∧
    -Real.log (1280 / 1603) ≤ (56254199 / 250000000) := by
  have h := checkLog_sound (w := (323 / 2883)) (n := 12)
    (lo := (45003359 / 200000000)) (hi := (56254199 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1603 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1603 / 1280) = 1/(1280 / 1603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (45003359 / 200000000) (56254199 / 250000000) (Real.log (1603 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1603 / 1280) = -Real.log (1280 / 1603) := by
    rw [show ((1603 / 1280) : ℝ) = ((1280 / 1603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (58162393 / 200000000) ≤ -Real.log (957 / 1280) ∧
    -Real.log (957 / 1280) ≤ (145405983 / 500000000) := by
  have h := checkLog_sound (w := (323 / 2237)) (n := 12)
    (lo := (58162393 / 200000000)) (hi := (145405983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 957) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 957) = 1/(957 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-145405983 / 500000000) (-58162393 / 200000000) (Real.log (957 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (224548813 / 1000000000) ≤ -Real.log (5120 / 6409) ∧
    -Real.log (5120 / 6409) ≤ (112274407 / 500000000) := by
  have h := checkLog_sound (w := (1289 / 11529)) (n := 12)
    (lo := (224548813 / 1000000000)) (hi := (112274407 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6409 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6409 / 5120) = 1/(5120 / 6409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (224548813 / 1000000000) (112274407 / 500000000) (Real.log (6409 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6409 / 5120) = -Real.log (5120 / 6409) := by
    rw [show ((6409 / 5120) : ℝ) = ((5120 / 6409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (290028573 / 1000000000) ≤ -Real.log (3831 / 5120) ∧
    -Real.log (3831 / 5120) ≤ (145014287 / 500000000) := by
  have h := checkLog_sound (w := (1289 / 8951)) (n := 12)
    (lo := (290028573 / 1000000000)) (hi := (145014287 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3831) = 1/(3831 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-145014287 / 500000000) (-290028573 / 1000000000) (Real.log (3831 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (8212207 / 50000000) ≤ -Real.log (500000 / 589251) ∧
    -Real.log (500000 / 589251) ≤ (164244141 / 1000000000) := by
  have h := checkLog_sound (w := (89251 / 1089251)) (n := 12)
    (lo := (8212207 / 50000000)) (hi := (164244141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((589251 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(589251 / 500000) = 1/(500000 / 589251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (8212207 / 50000000) (164244141 / 1000000000) (Real.log (589251 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (589251 / 500000) = -Real.log (500000 / 589251) := by
    rw [show ((589251 / 500000) : ℝ) = ((500000 / 589251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (12289111 / 62500000) ≤ -Real.log (410749 / 500000) ∧
    -Real.log (410749 / 500000) ≤ (196625777 / 1000000000) := by
  have h := checkLog_sound (w := (89251 / 910749)) (n := 12)
    (lo := (12289111 / 62500000)) (hi := (196625777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 410749) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 410749) = 1/(410749 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-196625777 / 1000000000) (-12289111 / 62500000) (Real.log (410749 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (164599613 / 1000000000) ≤ -Real.log (1000000 / 1178921) ∧
    -Real.log (1000000 / 1178921) ≤ (82299807 / 500000000) := by
  have h := checkLog_sound (w := (178921 / 2178921)) (n := 12)
    (lo := (164599613 / 1000000000)) (hi := (82299807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1178921 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1178921 / 1000000) = 1/(1000000 / 1178921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (164599613 / 1000000000) (82299807 / 500000000) (Real.log (1178921 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1178921 / 1000000) = -Real.log (1000000 / 1178921) := by
    rw [show ((1178921 / 1000000) : ℝ) = ((1000000 / 1178921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3942719 / 20000000) ≤ -Real.log (821079 / 1000000) ∧
    -Real.log (821079 / 1000000) ≤ (197135951 / 1000000000) := by
  have h := checkLog_sound (w := (178921 / 1821079)) (n := 12)
    (lo := (3942719 / 20000000)) (hi := (197135951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 821079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 821079) = 1/(821079 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-197135951 / 1000000000) (-3942719 / 20000000) (Real.log (821079 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (11986531 / 100000000) ≤ -Real.log (200000 / 225469) ∧
    -Real.log (200000 / 225469) ≤ (119865311 / 1000000000) := by
  have h := checkLog_sound (w := (25469 / 425469)) (n := 12)
    (lo := (11986531 / 100000000)) (hi := (119865311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((225469 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(225469 / 200000) = 1/(200000 / 225469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (11986531 / 100000000) (119865311 / 1000000000) (Real.log (225469 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (225469 / 200000) = -Real.log (200000 / 225469) := by
    rw [show ((225469 / 200000) : ℝ) = ((200000 / 225469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (13621499 / 100000000) ≤ -Real.log (174531 / 200000) ∧
    -Real.log (174531 / 200000) ≤ (136214991 / 1000000000) := by
  have h := checkLog_sound (w := (25469 / 374531)) (n := 12)
    (lo := (13621499 / 100000000)) (hi := (136214991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 174531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 174531) = 1/(174531 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-136214991 / 1000000000) (-13621499 / 100000000) (Real.log (174531 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (60067467 / 500000000) ≤ -Real.log (1000000 / 1127649) ∧
    -Real.log (1000000 / 1127649) ≤ (24026987 / 200000000) := by
  have h := checkLog_sound (w := (127649 / 2127649)) (n := 12)
    (lo := (60067467 / 500000000)) (hi := (24026987 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1127649 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1127649 / 1000000) = 1/(1000000 / 1127649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (60067467 / 500000000) (24026987 / 200000000) (Real.log (1127649 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1127649 / 1000000) = -Real.log (1000000 / 1127649) := by
    rw [show ((1127649 / 1000000) : ℝ) = ((1000000 / 1127649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (136563413 / 1000000000) ≤ -Real.log (872351 / 1000000) ∧
    -Real.log (872351 / 1000000) ≤ (68281707 / 500000000) := by
  have h := checkLog_sound (w := (127649 / 1872351)) (n := 12)
    (lo := (136563413 / 1000000000)) (hi := (68281707 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 872351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 872351) = 1/(872351 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-68281707 / 500000000) (-136563413 / 1000000000) (Real.log (872351 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (257288693 / 500000000) ≤ -Real.log (250000000000 / 418232837379) ∧
    -Real.log (250000000000 / 418232837379) ≤ (514577387 / 1000000000) := by
  have h := checkLog_sound (w := (168232837379 / 668232837379)) (n := 12)
    (lo := (257288693 / 500000000)) (hi := (514577387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((418232837379 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(418232837379 / 250000000000) = 1/(250000000000 / 418232837379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (257288693 / 500000000) (514577387 / 1000000000) (Real.log (418232837379 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (418232837379 / 250000000000) = -Real.log (250000000000 / 418232837379) := by
    rw [show ((418232837379 / 250000000000) : ℝ) = ((250000000000 / 418232837379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (515828761 / 1000000000) ≤ -Real.log (500000000000 / 837513061651) ∧
    -Real.log (500000000000 / 837513061651) ≤ (257914381 / 500000000) := by
  have h := checkLog_sound (w := (337513061651 / 1337513061651)) (n := 12)
    (lo := (515828761 / 1000000000)) (hi := (257914381 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((837513061651 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(837513061651 / 500000000000) = 1/(500000000000 / 837513061651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (515828761 / 1000000000) (257914381 / 500000000) (Real.log (837513061651 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (837513061651 / 500000000000) = -Real.log (500000000000 / 837513061651) := by
    rw [show ((837513061651 / 500000000000) : ℝ) = ((500000000000 / 837513061651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (90217479 / 250000000) ≤ -Real.log (500000000000 / 717288417013) ∧
    -Real.log (500000000000 / 717288417013) ≤ (360869917 / 1000000000) := by
  have h := checkLog_sound (w := (217288417013 / 1217288417013)) (n := 12)
    (lo := (90217479 / 250000000)) (hi := (360869917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((717288417013 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(717288417013 / 500000000000) = 1/(500000000000 / 717288417013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (90217479 / 250000000) (360869917 / 1000000000) (Real.log (717288417013 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (717288417013 / 500000000000) = -Real.log (500000000000 / 717288417013) := by
    rw [show ((717288417013 / 500000000000) : ℝ) = ((500000000000 / 717288417013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (361735563 / 1000000000) ≤ -Real.log (250000000000 / 358954802157) ∧
    -Real.log (250000000000 / 358954802157) ≤ (90433891 / 250000000) := by
  have h := checkLog_sound (w := (108954802157 / 608954802157)) (n := 12)
    (lo := (361735563 / 1000000000)) (hi := (90433891 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((358954802157 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(358954802157 / 250000000000) = 1/(250000000000 / 358954802157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (361735563 / 1000000000) (90433891 / 250000000) (Real.log (358954802157 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (358954802157 / 250000000000) = -Real.log (250000000000 / 358954802157) := by
    rw [show ((358954802157 / 250000000000) : ℝ) = ((250000000000 / 358954802157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (2560803 / 10000000) ≤ -Real.log (250000000000 / 322964115257) ∧
    -Real.log (250000000000 / 322964115257) ≤ (256080301 / 1000000000) := by
  have h := checkLog_sound (w := (72964115257 / 572964115257)) (n := 12)
    (lo := (2560803 / 10000000)) (hi := (256080301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((322964115257 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(322964115257 / 250000000000) = 1/(250000000000 / 322964115257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2560803 / 10000000) (256080301 / 1000000000) (Real.log (322964115257 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (322964115257 / 250000000000) = -Real.log (250000000000 / 322964115257) := by
    rw [show ((322964115257 / 250000000000) : ℝ) = ((250000000000 / 322964115257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (256698347 / 1000000000) ≤ -Real.log (62500000000 / 80790945961) ∧
    -Real.log (62500000000 / 80790945961) ≤ (64174587 / 250000000) := by
  have h := checkLog_sound (w := (18290945961 / 143290945961)) (n := 12)
    (lo := (256698347 / 1000000000)) (hi := (64174587 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80790945961 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80790945961 / 62500000000) = 1/(62500000000 / 80790945961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (256698347 / 1000000000) (64174587 / 250000000) (Real.log (80790945961 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (80790945961 / 62500000000) = -Real.log (62500000000 / 80790945961) := by
    rw [show ((80790945961 / 62500000000) : ℝ) = ((62500000000 / 80790945961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (8214239 / 500000000) ≤ -Real.log (983705732799 / 1000000000000) ∧
    -Real.log (983705732799 / 1000000000000) ≤ (16428479 / 1000000000) := by
  have h := checkLog_sound (w := (16294267201 / 1983705732799)) (n := 12)
    (lo := (8214239 / 500000000)) (hi := (16428479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 983705732799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 983705732799) = 1/(983705732799 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-16428479 / 1000000000) (-8214239 / 500000000) (Real.log (983705732799 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (16349679 / 1000000000) ≤ -Real.log (39351330039 / 40000000000) ∧
    -Real.log (39351330039 / 40000000000) ≤ (204371 / 12500000) := by
  have h := checkLog_sound (w := (648669961 / 79351330039)) (n := 12)
    (lo := (16349679 / 1000000000)) (hi := (204371 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39351330039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39351330039) = 1/(39351330039 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-204371 / 12500000) (-16349679 / 1000000000) (Real.log (39351330039 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell003

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell004Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell004
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

theorem reflection_log_1_neg : (225484559 / 1000000000) ≤ -Real.log (1024 / 1283) ∧
    -Real.log (1024 / 1283) ≤ (2818557 / 12500000) := by
  have h := checkLog_sound (w := (259 / 2307)) (n := 12)
    (lo := (225484559 / 1000000000)) (hi := (2818557 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1283 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1283 / 1024) = 1/(1024 / 1283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (225484559 / 1000000000) (2818557 / 12500000) (Real.log (1283 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1283 / 1024) = -Real.log (1024 / 1283) := by
    rw [show ((1283 / 1024) : ℝ) = ((1024 / 1283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (291595971 / 1000000000) ≤ -Real.log (765 / 1024) ∧
    -Real.log (765 / 1024) ≤ (72898993 / 250000000) := by
  have h := checkLog_sound (w := (259 / 1789)) (n := 12)
    (lo := (291595971 / 1000000000)) (hi := (72898993 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 765) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 765) = 1/(765 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-72898993 / 250000000) (-291595971 / 1000000000) (Real.log (765 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (45003359 / 200000000) ≤ -Real.log (1280 / 1603) ∧
    -Real.log (1280 / 1603) ≤ (56254199 / 250000000) := by
  have h := checkLog_sound (w := (323 / 2883)) (n := 12)
    (lo := (45003359 / 200000000)) (hi := (56254199 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1603 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1603 / 1280) = 1/(1280 / 1603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (45003359 / 200000000) (56254199 / 250000000) (Real.log (1603 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1603 / 1280) = -Real.log (1280 / 1603) := by
    rw [show ((1603 / 1280) : ℝ) = ((1280 / 1603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (58162393 / 200000000) ≤ -Real.log (957 / 1280) ∧
    -Real.log (957 / 1280) ≤ (145405983 / 500000000) := by
  have h := checkLog_sound (w := (323 / 2237)) (n := 12)
    (lo := (58162393 / 200000000)) (hi := (145405983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 957) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 957) = 1/(957 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-145405983 / 500000000) (-58162393 / 200000000) (Real.log (957 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (32919753 / 200000000) ≤ -Real.log (25000 / 29473) ∧
    -Real.log (25000 / 29473) ≤ (82299383 / 500000000) := by
  have h := checkLog_sound (w := (4473 / 54473)) (n := 12)
    (lo := (32919753 / 200000000)) (hi := (82299383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29473 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29473 / 25000) = 1/(25000 / 29473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (32919753 / 200000000) (82299383 / 500000000) (Real.log (29473 / 25000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (29473 / 25000) = -Real.log (25000 / 29473) := by
    rw [show ((29473 / 25000) : ℝ) = ((25000 / 29473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (49283683 / 250000000) ≤ -Real.log (20527 / 25000) ∧
    -Real.log (20527 / 25000) ≤ (197134733 / 1000000000) := by
  have h := checkLog_sound (w := (4473 / 45527)) (n := 12)
    (lo := (49283683 / 250000000)) (hi := (197134733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 20527) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 20527) = 1/(20527 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-197134733 / 1000000000) (-49283683 / 250000000) (Real.log (20527 / 25000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (322176 / 1953125) ≤ -Real.log (1000000 / 1179339) ∧
    -Real.log (1000000 / 1179339) ≤ (164954113 / 1000000000) := by
  have h := checkLog_sound (w := (179339 / 2179339)) (n := 12)
    (lo := (322176 / 1953125)) (hi := (164954113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1179339 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1179339 / 1000000) = 1/(1000000 / 1179339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (322176 / 1953125) (164954113 / 1000000000) (Real.log (1179339 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1179339 / 1000000) = -Real.log (1000000 / 1179339) := by
    rw [show ((1179339 / 1000000) : ℝ) = ((1000000 / 1179339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (39529033 / 200000000) ≤ -Real.log (820661 / 1000000) ∧
    -Real.log (820661 / 1000000) ≤ (98822583 / 500000000) := by
  have h := checkLog_sound (w := (179339 / 1820661)) (n := 12)
    (lo := (39529033 / 200000000)) (hi := (98822583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 820661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 820661) = 1/(820661 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-98822583 / 500000000) (-39529033 / 200000000) (Real.log (820661 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (120134047 / 1000000000) ≤ -Real.log (31250 / 35239) ∧
    -Real.log (31250 / 35239) ≤ (3754189 / 31250000) := by
  have h := checkLog_sound (w := (3989 / 66489)) (n := 12)
    (lo := (120134047 / 1000000000)) (hi := (3754189 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((35239 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(35239 / 31250) = 1/(31250 / 35239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (120134047 / 1000000000) (3754189 / 31250000) (Real.log (35239 / 31250)) := by
  have h := reflection_log_9_neg
  have he : Real.log (35239 / 31250) = -Real.log (31250 / 35239) := by
    rw [show ((35239 / 31250) : ℝ) = ((31250 / 35239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (68281133 / 500000000) ≤ -Real.log (27261 / 31250) ∧
    -Real.log (27261 / 31250) ≤ (136562267 / 1000000000) := by
  have h := checkLog_sound (w := (3989 / 58511)) (n := 12)
    (lo := (68281133 / 500000000)) (hi := (136562267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 27261) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 27261) = 1/(27261 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-136562267 / 1000000000) (-68281133 / 500000000) (Real.log (27261 / 31250)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (60201799 / 500000000) ≤ -Real.log (62500 / 70497) ∧
    -Real.log (62500 / 70497) ≤ (120403599 / 1000000000) := by
  have h := checkLog_sound (w := (7997 / 132997)) (n := 12)
    (lo := (60201799 / 500000000)) (hi := (120403599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((70497 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(70497 / 62500) = 1/(62500 / 70497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (60201799 / 500000000) (120403599 / 1000000000) (Real.log (70497 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (70497 / 62500) = -Real.log (62500 / 70497) := by
    rw [show ((70497 / 62500) : ℝ) = ((62500 / 70497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (13691081 / 100000000) ≤ -Real.log (54503 / 62500) ∧
    -Real.log (54503 / 62500) ≤ (136910811 / 1000000000) := by
  have h := checkLog_sound (w := (7997 / 117003)) (n := 12)
    (lo := (13691081 / 100000000)) (hi := (136910811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 54503) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 54503) = 1/(54503 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-136910811 / 1000000000) (-13691081 / 100000000) (Real.log (54503 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (515828761 / 1000000000) ≤ -Real.log (10000000000 / 16750261233) ∧
    -Real.log (10000000000 / 16750261233) ≤ (257914381 / 500000000) := by
  have h := checkLog_sound (w := (6750261233 / 26750261233)) (n := 12)
    (lo := (515828761 / 1000000000)) (hi := (257914381 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16750261233 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16750261233 / 10000000000) = 1/(10000000000 / 16750261233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (515828761 / 1000000000) (257914381 / 500000000) (Real.log (16750261233 / 10000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (16750261233 / 10000000000) = -Real.log (10000000000 / 16750261233) := by
    rw [show ((16750261233 / 10000000000) : ℝ) = ((10000000000 / 16750261233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (51708053 / 100000000) ≤ -Real.log (31250000000 / 52410130719) ∧
    -Real.log (31250000000 / 52410130719) ≤ (517080531 / 1000000000) := by
  have h := checkLog_sound (w := (21160130719 / 83660130719)) (n := 12)
    (lo := (51708053 / 100000000)) (hi := (517080531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((52410130719 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(52410130719 / 31250000000) = 1/(31250000000 / 52410130719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (51708053 / 100000000) (517080531 / 1000000000) (Real.log (52410130719 / 31250000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (52410130719 / 31250000000) = -Real.log (31250000000 / 52410130719) := by
    rw [show ((52410130719 / 31250000000) : ℝ) = ((31250000000 / 52410130719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (361733497 / 1000000000) ≤ -Real.log (500000000000 / 717908121011) ∧
    -Real.log (500000000000 / 717908121011) ≤ (180866749 / 500000000) := by
  have h := checkLog_sound (w := (217908121011 / 1217908121011)) (n := 12)
    (lo := (361733497 / 1000000000)) (hi := (180866749 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((717908121011 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(717908121011 / 500000000000) = 1/(500000000000 / 717908121011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (361733497 / 1000000000) (180866749 / 500000000) (Real.log (717908121011 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (717908121011 / 500000000000) = -Real.log (500000000000 / 717908121011) := by
    rw [show ((717908121011 / 500000000000) : ℝ) = ((500000000000 / 717908121011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (362599277 / 1000000000) ≤ -Real.log (500000000000 / 718529941109) ∧
    -Real.log (500000000000 / 718529941109) ≤ (181299639 / 500000000) := by
  have h := checkLog_sound (w := (218529941109 / 1218529941109)) (n := 12)
    (lo := (362599277 / 1000000000)) (hi := (181299639 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((718529941109 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(718529941109 / 500000000000) = 1/(500000000000 / 718529941109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (362599277 / 1000000000) (181299639 / 500000000) (Real.log (718529941109 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (718529941109 / 500000000000) = -Real.log (500000000000 / 718529941109) := by
    rw [show ((718529941109 / 500000000000) : ℝ) = ((500000000000 / 718529941109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (128348157 / 500000000) ≤ -Real.log (250000000000 / 323163126811) ∧
    -Real.log (250000000000 / 323163126811) ≤ (51339263 / 200000000) := by
  have h := checkLog_sound (w := (73163126811 / 573163126811)) (n := 12)
    (lo := (128348157 / 500000000)) (hi := (51339263 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((323163126811 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(323163126811 / 250000000000) = 1/(250000000000 / 323163126811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (128348157 / 500000000) (51339263 / 200000000) (Real.log (323163126811 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (323163126811 / 250000000000) = -Real.log (250000000000 / 323163126811) := by
    rw [show ((323163126811 / 250000000000) : ℝ) = ((250000000000 / 323163126811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (257314409 / 1000000000) ≤ -Real.log (500000000000 / 646725868301) ∧
    -Real.log (500000000000 / 646725868301) ≤ (25731441 / 100000000) := by
  have h := checkLog_sound (w := (146725868301 / 1146725868301)) (n := 12)
    (lo := (257314409 / 1000000000)) (hi := (25731441 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((646725868301 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(646725868301 / 500000000000) = 1/(500000000000 / 646725868301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (257314409 / 1000000000) (25731441 / 100000000) (Real.log (646725868301 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (646725868301 / 500000000000) = -Real.log (500000000000 / 646725868301) := by
    rw [show ((646725868301 / 500000000000) : ℝ) = ((500000000000 / 646725868301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (16507211 / 1000000000) ≤ -Real.log (3842297991 / 3906250000) ∧
    -Real.log (3842297991 / 3906250000) ≤ (4126803 / 250000000) := by
  have h := checkLog_sound (w := (63952009 / 7748547991)) (n := 12)
    (lo := (16507211 / 1000000000)) (hi := (4126803 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3842297991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3842297991) = 1/(3842297991 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-4126803 / 250000000) (-16507211 / 1000000000) (Real.log (3842297991 / 3906250000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (16428219 / 1000000000) ≤ -Real.log (960650379 / 976562500) ∧
    -Real.log (960650379 / 976562500) ≤ (821411 / 50000000) := by
  have h := checkLog_sound (w := (15912121 / 1937212879)) (n := 12)
    (lo := (16428219 / 1000000000)) (hi := (821411 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 960650379) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 960650379) = 1/(960650379 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-821411 / 50000000) (-16428219 / 1000000000) (Real.log (960650379 / 976562500)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell004

end


