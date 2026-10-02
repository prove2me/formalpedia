-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell227Logs__6
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell227Logs__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T17:44:18.867119+00:00
-- url     : https://prove2.me/theorems/29811658-d98f-4d54-a678-86db37949e7d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell227Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell228…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell227Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell228Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell229Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell230Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell231Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell232Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell227Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell228Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell229Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell230Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell231Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell232Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell227Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell228Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell229Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell230Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell231Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell232Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell227Logs (+5 modules: GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell228Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell229Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell230Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell231Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell232Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell227Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell227
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

theorem reflection_log_1_neg : (8117107 / 25000000) ≤ -Real.log (1280 / 1771) ∧
    -Real.log (1280 / 1771) ≤ (324684281 / 1000000000) := by
  have h := checkLog_sound (w := (491 / 3051)) (n := 12)
    (lo := (8117107 / 25000000)) (hi := (324684281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1771 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1771 / 1280) = 1/(1280 / 1771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (8117107 / 25000000) (324684281 / 1000000000) (Real.log (1771 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1771 / 1280) = -Real.log (1280 / 1771) := by
    rw [show ((1771 / 1280) : ℝ) = ((1280 / 1771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (120962259 / 250000000) ≤ -Real.log (789 / 1280) ∧
    -Real.log (789 / 1280) ≤ (483849037 / 1000000000) := by
  have h := checkLog_sound (w := (491 / 2069)) (n := 12)
    (lo := (120962259 / 250000000)) (hi := (483849037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 789) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 789) = 1/(789 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-483849037 / 1000000000) (-120962259 / 250000000) (Real.log (789 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (324260701 / 1000000000) ≤ -Real.log (5120 / 7081) ∧
    -Real.log (5120 / 7081) ≤ (162130351 / 500000000) := by
  have h := checkLog_sound (w := (1961 / 12201)) (n := 12)
    (lo := (324260701 / 1000000000)) (hi := (162130351 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7081 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7081 / 5120) = 1/(5120 / 7081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (324260701 / 1000000000) (162130351 / 500000000) (Real.log (7081 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7081 / 5120) = -Real.log (5120 / 7081) := by
    rw [show ((7081 / 5120) : ℝ) = ((5120 / 7081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (482898917 / 1000000000) ≤ -Real.log (3159 / 5120) ∧
    -Real.log (3159 / 5120) ≤ (241449459 / 500000000) := by
  have h := checkLog_sound (w := (1961 / 8279)) (n := 12)
    (lo := (482898917 / 1000000000)) (hi := (241449459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3159) = 1/(3159 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-241449459 / 500000000) (-482898917 / 1000000000) (Real.log (3159 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (241054979 / 1000000000) ≤ -Real.log (1000000 / 1272591) ∧
    -Real.log (1000000 / 1272591) ≤ (12052749 / 50000000) := by
  have h := checkLog_sound (w := (272591 / 2272591)) (n := 12)
    (lo := (241054979 / 1000000000)) (hi := (12052749 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1272591 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1272591 / 1000000) = 1/(1000000 / 1272591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (241054979 / 1000000000) (12052749 / 50000000) (Real.log (1272591 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1272591 / 1000000) = -Real.log (1000000 / 1272591) := by
    rw [show ((1272591 / 1000000) : ℝ) = ((1000000 / 1272591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (318266373 / 1000000000) ≤ -Real.log (727409 / 1000000) ∧
    -Real.log (727409 / 1000000) ≤ (159133187 / 500000000) := by
  have h := checkLog_sound (w := (272591 / 1727409)) (n := 12)
    (lo := (318266373 / 1000000000)) (hi := (159133187 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 727409) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 727409) = 1/(727409 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-159133187 / 500000000) (-318266373 / 1000000000) (Real.log (727409 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (120694051 / 500000000) ≤ -Real.log (200000 / 254603) ∧
    -Real.log (200000 / 254603) ≤ (241388103 / 1000000000) := by
  have h := checkLog_sound (w := (54603 / 454603)) (n := 12)
    (lo := (120694051 / 500000000)) (hi := (241388103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((254603 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(254603 / 200000) = 1/(200000 / 254603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (120694051 / 500000000) (241388103 / 1000000000) (Real.log (254603 / 200000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (254603 / 200000) = -Real.log (200000 / 254603) := by
    rw [show ((254603 / 200000) : ℝ) = ((200000 / 254603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (159424717 / 500000000) ≤ -Real.log (145397 / 200000) ∧
    -Real.log (145397 / 200000) ≤ (63769887 / 200000000) := by
  have h := checkLog_sound (w := (54603 / 345397)) (n := 12)
    (lo := (159424717 / 500000000)) (hi := (63769887 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 145397) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 145397) = 1/(145397 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-63769887 / 200000000) (-159424717 / 500000000) (Real.log (145397 / 200000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (179652163 / 1000000000) ≤ -Real.log (1000000 / 1196801) ∧
    -Real.log (1000000 / 1196801) ≤ (44913041 / 250000000) := by
  have h := checkLog_sound (w := (196801 / 2196801)) (n := 12)
    (lo := (179652163 / 1000000000)) (hi := (44913041 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1196801 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1196801 / 1000000) = 1/(1000000 / 1196801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (179652163 / 1000000000) (44913041 / 250000000) (Real.log (1196801 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1196801 / 1000000) = -Real.log (1000000 / 1196801) := by
    rw [show ((1196801 / 1000000) : ℝ) = ((1000000 / 1196801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (8766111 / 40000000) ≤ -Real.log (803199 / 1000000) ∧
    -Real.log (803199 / 1000000) ≤ (27394097 / 125000000) := by
  have h := checkLog_sound (w := (196801 / 1803199)) (n := 12)
    (lo := (8766111 / 40000000)) (hi := (27394097 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 803199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 803199) = 1/(803199 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-27394097 / 125000000) (-8766111 / 40000000) (Real.log (803199 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (11244917 / 62500000) ≤ -Real.log (3125 / 3741) ∧
    -Real.log (3125 / 3741) ≤ (179918673 / 1000000000) := by
  have h := checkLog_sound (w := (308 / 3433)) (n := 12)
    (lo := (11244917 / 62500000)) (hi := (179918673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3741 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3741 / 3125) = 1/(3125 / 3741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (11244917 / 62500000) (179918673 / 1000000000) (Real.log (3741 / 3125)) := by
  have h := reflection_log_11_neg
  have he : Real.log (3741 / 3125) = -Real.log (3125 / 3741) := by
    rw [show ((3741 / 3125) : ℝ) = ((3125 / 3741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (43910003 / 200000000) ≤ -Real.log (2509 / 3125) ∧
    -Real.log (2509 / 3125) ≤ (3430469 / 15625000) := by
  have h := checkLog_sound (w := (308 / 2817)) (n := 12)
    (lo := (43910003 / 200000000)) (hi := (3430469 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2509) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3125 / 2509) = 1/(2509 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3430469 / 15625000) (-43910003 / 200000000) (Real.log (2509 / 3125)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (403579809 / 500000000) ≤ -Real.log (50000000000 / 112076606521) ∧
    -Real.log (50000000000 / 112076606521) ≤ (40357981 / 50000000) := by
  have h := checkLog_sound (w := (12076606521 / 212076606521)) (n := 12)
    (lo := (57006219 / 500000000)) (hi := (114012439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((112076606521 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(112076606521 / 100000000000) = 1/(50000000000 / 112076606521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (403579809 / 500000000) (40357981 / 50000000) (Real.log (112076606521 / 50000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (112076606521 / 50000000000) = -Real.log (50000000000 / 112076606521) := by
    rw [show ((112076606521 / 50000000000) : ℝ) = ((50000000000 / 112076606521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (202133329 / 250000000) ≤ -Real.log (125000000000 / 280576679341) ∧
    -Real.log (125000000000 / 280576679341) ≤ (404266659 / 500000000) := by
  have h := checkLog_sound (w := (30576679341 / 530576679341)) (n := 12)
    (lo := (14423267 / 125000000)) (hi := (115386137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((280576679341 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(280576679341 / 250000000000) = 1/(125000000000 / 280576679341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (202133329 / 250000000) (404266659 / 500000000) (Real.log (280576679341 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (280576679341 / 125000000000) = -Real.log (125000000000 / 280576679341) := by
    rw [show ((280576679341 / 125000000000) : ℝ) = ((125000000000 / 280576679341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (559321353 / 1000000000) ≤ -Real.log (500000000000 / 874742407641) ∧
    -Real.log (500000000000 / 874742407641) ≤ (279660677 / 500000000) := by
  have h := checkLog_sound (w := (374742407641 / 1374742407641)) (n := 12)
    (lo := (559321353 / 1000000000)) (hi := (279660677 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((874742407641 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(874742407641 / 500000000000) = 1/(500000000000 / 874742407641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (559321353 / 1000000000) (279660677 / 500000000) (Real.log (874742407641 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (874742407641 / 500000000000) = -Real.log (500000000000 / 874742407641) := by
    rw [show ((874742407641 / 500000000000) : ℝ) = ((500000000000 / 874742407641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (560237537 / 1000000000) ≤ -Real.log (250000000000 / 437772099837) ∧
    -Real.log (250000000000 / 437772099837) ≤ (280118769 / 500000000) := by
  have h := checkLog_sound (w := (187772099837 / 687772099837)) (n := 12)
    (lo := (560237537 / 1000000000)) (hi := (280118769 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((437772099837 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(437772099837 / 250000000000) = 1/(250000000000 / 437772099837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (560237537 / 1000000000) (280118769 / 500000000) (Real.log (437772099837 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (437772099837 / 250000000000) = -Real.log (250000000000 / 437772099837) := by
    rw [show ((437772099837 / 250000000000) : ℝ) = ((250000000000 / 437772099837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (199402469 / 500000000) ≤ -Real.log (100000000000 / 149004294079) ∧
    -Real.log (100000000000 / 149004294079) ≤ (398804939 / 1000000000) := by
  have h := checkLog_sound (w := (49004294079 / 249004294079)) (n := 12)
    (lo := (199402469 / 500000000)) (hi := (398804939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149004294079 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149004294079 / 100000000000) = 1/(100000000000 / 149004294079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (199402469 / 500000000) (398804939 / 1000000000) (Real.log (149004294079 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (149004294079 / 100000000000) = -Real.log (100000000000 / 149004294079) := by
    rw [show ((149004294079 / 100000000000) : ℝ) = ((100000000000 / 149004294079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (399468687 / 1000000000) ≤ -Real.log (50000000000 / 74551614189) ∧
    -Real.log (50000000000 / 74551614189) ≤ (24966793 / 62500000) := by
  have h := checkLog_sound (w := (24551614189 / 124551614189)) (n := 12)
    (lo := (399468687 / 1000000000)) (hi := (24966793 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74551614189 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74551614189 / 50000000000) = 1/(50000000000 / 74551614189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (399468687 / 1000000000) (24966793 / 62500000) (Real.log (74551614189 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (74551614189 / 50000000000) = -Real.log (50000000000 / 74551614189) := by
    rw [show ((74551614189 / 50000000000) : ℝ) = ((50000000000 / 74551614189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (39631343 / 1000000000) ≤ -Real.log (9386169 / 9765625) ∧
    -Real.log (9386169 / 9765625) ≤ (2476959 / 62500000) := by
  have h := checkLog_sound (w := (189728 / 9575897)) (n := 12)
    (lo := (39631343 / 1000000000)) (hi := (2476959 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9765625 / 9386169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9765625 / 9386169) = 1/(9386169 / 9765625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-2476959 / 62500000) (-39631343 / 1000000000) (Real.log (9386169 / 9765625)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (39500611 / 1000000000) ≤ -Real.log (961269366399 / 1000000000000) ∧
    -Real.log (961269366399 / 1000000000000) ≤ (9875153 / 250000000) := by
  have h := checkLog_sound (w := (38730633601 / 1961269366399)) (n := 12)
    (lo := (39500611 / 1000000000)) (hi := (9875153 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 961269366399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 961269366399) = 1/(961269366399 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-9875153 / 250000000) (-39500611 / 1000000000) (Real.log (961269366399 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell227

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell228Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell228
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

theorem reflection_log_1_neg : (2031923 / 6250000) ≤ -Real.log (5120 / 7087) ∧
    -Real.log (5120 / 7087) ≤ (325107681 / 1000000000) := by
  have h := checkLog_sound (w := (1967 / 12207)) (n := 12)
    (lo := (2031923 / 6250000)) (hi := (325107681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7087 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7087 / 5120) = 1/(5120 / 7087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (2031923 / 6250000) (325107681 / 1000000000) (Real.log (7087 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7087 / 5120) = -Real.log (5120 / 7087) := by
    rw [show ((7087 / 5120) : ℝ) = ((5120 / 7087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (242400029 / 500000000) ≤ -Real.log (3153 / 5120) ∧
    -Real.log (3153 / 5120) ≤ (484800059 / 1000000000) := by
  have h := checkLog_sound (w := (1967 / 8273)) (n := 12)
    (lo := (242400029 / 500000000)) (hi := (484800059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3153) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3153) = 1/(3153 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-484800059 / 1000000000) (-242400029 / 500000000) (Real.log (3153 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (8117107 / 25000000) ≤ -Real.log (1280 / 1771) ∧
    -Real.log (1280 / 1771) ≤ (324684281 / 1000000000) := by
  have h := checkLog_sound (w := (491 / 3051)) (n := 12)
    (lo := (8117107 / 25000000)) (hi := (324684281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1771 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1771 / 1280) = 1/(1280 / 1771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (8117107 / 25000000) (324684281 / 1000000000) (Real.log (1771 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1771 / 1280) = -Real.log (1280 / 1771) := by
    rw [show ((1771 / 1280) : ℝ) = ((1280 / 1771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (120962259 / 250000000) ≤ -Real.log (789 / 1280) ∧
    -Real.log (789 / 1280) ≤ (483849037 / 1000000000) := by
  have h := checkLog_sound (w := (491 / 2069)) (n := 12)
    (lo := (120962259 / 250000000)) (hi := (483849037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 789) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 789) = 1/(789 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-483849037 / 1000000000) (-120962259 / 250000000) (Real.log (789 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (241387317 / 1000000000) ≤ -Real.log (500000 / 636507) ∧
    -Real.log (500000 / 636507) ≤ (120693659 / 500000000) := by
  have h := checkLog_sound (w := (136507 / 1136507)) (n := 12)
    (lo := (241387317 / 1000000000)) (hi := (120693659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((636507 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(636507 / 500000) = 1/(500000 / 636507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (241387317 / 1000000000) (120693659 / 500000000) (Real.log (636507 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (636507 / 500000) = -Real.log (500000 / 636507) := by
    rw [show ((636507 / 500000) : ℝ) = ((500000 / 636507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (159424029 / 500000000) ≤ -Real.log (363493 / 500000) ∧
    -Real.log (363493 / 500000) ≤ (318848059 / 1000000000) := by
  have h := checkLog_sound (w := (136507 / 863493)) (n := 12)
    (lo := (159424029 / 500000000)) (hi := (318848059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 363493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 363493) = 1/(363493 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-318848059 / 1000000000) (-159424029 / 500000000) (Real.log (363493 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (241720329 / 1000000000) ≤ -Real.log (500000 / 636719) ∧
    -Real.log (500000 / 636719) ≤ (24172033 / 100000000) := by
  have h := checkLog_sound (w := (136719 / 1136719)) (n := 12)
    (lo := (241720329 / 1000000000)) (hi := (24172033 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((636719 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(636719 / 500000) = 1/(500000 / 636719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (241720329 / 1000000000) (24172033 / 100000000) (Real.log (636719 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (636719 / 500000) = -Real.log (500000 / 636719) := by
    rw [show ((636719 / 500000) : ℝ) = ((500000 / 636719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (159715729 / 500000000) ≤ -Real.log (363281 / 500000) ∧
    -Real.log (363281 / 500000) ≤ (319431459 / 1000000000) := by
  have h := checkLog_sound (w := (136719 / 863281)) (n := 12)
    (lo := (159715729 / 500000000)) (hi := (319431459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 363281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 363281) = 1/(363281 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-319431459 / 1000000000) (-159715729 / 500000000) (Real.log (363281 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (44979459 / 250000000) ≤ -Real.log (1000000 / 1197119) ∧
    -Real.log (1000000 / 1197119) ≤ (179917837 / 1000000000) := by
  have h := checkLog_sound (w := (197119 / 2197119)) (n := 12)
    (lo := (44979459 / 250000000)) (hi := (179917837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1197119 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1197119 / 1000000) = 1/(1000000 / 1197119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (44979459 / 250000000) (179917837 / 1000000000) (Real.log (1197119 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1197119 / 1000000) = -Real.log (1000000 / 1197119) := by
    rw [show ((1197119 / 1000000) : ℝ) = ((1000000 / 1197119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (21954877 / 100000000) ≤ -Real.log (802881 / 1000000) ∧
    -Real.log (802881 / 1000000) ≤ (219548771 / 1000000000) := by
  have h := checkLog_sound (w := (197119 / 1802881)) (n := 12)
    (lo := (21954877 / 100000000)) (hi := (219548771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 802881) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 802881) = 1/(802881 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-219548771 / 1000000000) (-21954877 / 100000000) (Real.log (802881 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (180185109 / 1000000000) ≤ -Real.log (1000000 / 1197439) ∧
    -Real.log (1000000 / 1197439) ≤ (18018511 / 100000000) := by
  have h := checkLog_sound (w := (197439 / 2197439)) (n := 12)
    (lo := (180185109 / 1000000000)) (hi := (18018511 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1197439 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1197439 / 1000000) = 1/(1000000 / 1197439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (180185109 / 1000000000) (18018511 / 100000000) (Real.log (1197439 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1197439 / 1000000) = -Real.log (1000000 / 1197439) := by
    rw [show ((1197439 / 1000000) : ℝ) = ((1000000 / 1197439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (109973707 / 500000000) ≤ -Real.log (802561 / 1000000) ∧
    -Real.log (802561 / 1000000) ≤ (43989483 / 200000000) := by
  have h := checkLog_sound (w := (197439 / 1802561)) (n := 12)
    (lo := (109973707 / 500000000)) (hi := (43989483 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 802561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 802561) = 1/(802561 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-43989483 / 200000000) (-109973707 / 500000000) (Real.log (802561 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (202133329 / 250000000) ≤ -Real.log (500000000000 / 1122306717363) ∧
    -Real.log (500000000000 / 1122306717363) ≤ (404266659 / 500000000) := by
  have h := checkLog_sound (w := (122306717363 / 2122306717363)) (n := 12)
    (lo := (14423267 / 125000000)) (hi := (115386137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1122306717363 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1122306717363 / 1000000000000) = 1/(500000000000 / 1122306717363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (202133329 / 250000000) (404266659 / 500000000) (Real.log (1122306717363 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1122306717363 / 500000000000) = -Real.log (500000000000 / 1122306717363) := by
    rw [show ((1122306717363 / 500000000000) : ℝ) = ((500000000000 / 1122306717363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (404953869 / 500000000) ≤ -Real.log (500000000000 / 1123850301301) ∧
    -Real.log (500000000000 / 1123850301301) ≤ (40495387 / 50000000) := by
  have h := checkLog_sound (w := (123850301301 / 2123850301301)) (n := 12)
    (lo := (58380279 / 500000000)) (hi := (116760559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1123850301301 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1123850301301 / 1000000000000) = 1/(500000000000 / 1123850301301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (404953869 / 500000000) (40495387 / 50000000) (Real.log (1123850301301 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1123850301301 / 500000000000) = -Real.log (500000000000 / 1123850301301) := by
    rw [show ((1123850301301 / 500000000000) : ℝ) = ((500000000000 / 1123850301301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (35014711 / 62500000) ≤ -Real.log (250000000000 / 437771153777) ∧
    -Real.log (250000000000 / 437771153777) ≤ (560235377 / 1000000000) := by
  have h := checkLog_sound (w := (187771153777 / 687771153777)) (n := 12)
    (lo := (35014711 / 62500000)) (hi := (560235377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((437771153777 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(437771153777 / 250000000000) = 1/(250000000000 / 437771153777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (35014711 / 62500000) (560235377 / 1000000000) (Real.log (437771153777 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (437771153777 / 250000000000) = -Real.log (250000000000 / 437771153777) := by
    rw [show ((437771153777 / 250000000000) : ℝ) = ((250000000000 / 437771153777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (140287947 / 250000000) ≤ -Real.log (15625000000 / 27385782287) ∧
    -Real.log (15625000000 / 27385782287) ≤ (561151789 / 1000000000) := by
  have h := checkLog_sound (w := (11760782287 / 43010782287)) (n := 12)
    (lo := (140287947 / 250000000)) (hi := (561151789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27385782287 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27385782287 / 15625000000) = 1/(15625000000 / 27385782287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (140287947 / 250000000) (561151789 / 1000000000) (Real.log (27385782287 / 15625000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (27385782287 / 15625000000) = -Real.log (15625000000 / 27385782287) := by
    rw [show ((27385782287 / 15625000000) : ℝ) = ((15625000000 / 27385782287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (399466607 / 1000000000) ≤ -Real.log (25000000000 / 37275729529) ∧
    -Real.log (25000000000 / 37275729529) ≤ (24966663 / 62500000) := by
  have h := checkLog_sound (w := (12275729529 / 62275729529)) (n := 12)
    (lo := (399466607 / 1000000000)) (hi := (24966663 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37275729529 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37275729529 / 25000000000) = 1/(25000000000 / 37275729529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (399466607 / 1000000000) (24966663 / 62500000) (Real.log (37275729529 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (37275729529 / 25000000000) = -Real.log (25000000000 / 37275729529) := by
    rw [show ((37275729529 / 25000000000) : ℝ) = ((25000000000 / 37275729529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (400132523 / 1000000000) ≤ -Real.log (4000000000 / 5968089653) ∧
    -Real.log (4000000000 / 5968089653) ≤ (100033131 / 250000000) := by
  have h := checkLog_sound (w := (1968089653 / 9968089653)) (n := 12)
    (lo := (400132523 / 1000000000)) (hi := (100033131 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5968089653 / 4000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5968089653 / 4000000000) = 1/(4000000000 / 5968089653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (400132523 / 1000000000) (100033131 / 250000000) (Real.log (5968089653 / 4000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (5968089653 / 4000000000) = -Real.log (4000000000 / 5968089653) := by
    rw [show ((5968089653 / 4000000000) : ℝ) = ((4000000000 / 5968089653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (310643 / 7812500) ≤ -Real.log (961017841279 / 1000000000000) ∧
    -Real.log (961017841279 / 1000000000000) ≤ (7952461 / 200000000) := by
  have h := checkLog_sound (w := (38982158721 / 1961017841279)) (n := 12)
    (lo := (310643 / 7812500)) (hi := (7952461 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 961017841279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 961017841279) = 1/(961017841279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-7952461 / 200000000) (-310643 / 7812500) (Real.log (961017841279 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (39630933 / 1000000000) ≤ -Real.log (961144099839 / 1000000000000) ∧
    -Real.log (961144099839 / 1000000000000) ≤ (19815467 / 500000000) := by
  have h := checkLog_sound (w := (38855900161 / 1961144099839)) (n := 12)
    (lo := (39630933 / 1000000000)) (hi := (19815467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 961144099839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 961144099839) = 1/(961144099839 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-19815467 / 500000000) (-39630933 / 1000000000) (Real.log (961144099839 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell228

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell229Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell229
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

theorem reflection_log_1_neg : (325530901 / 1000000000) ≤ -Real.log (512 / 709) ∧
    -Real.log (512 / 709) ≤ (162765451 / 500000000) := by
  have h := checkLog_sound (w := (197 / 1221)) (n := 12)
    (lo := (325530901 / 1000000000)) (hi := (162765451 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((709 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(709 / 512) = 1/(512 / 709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (325530901 / 1000000000) (162765451 / 500000000) (Real.log (709 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (709 / 512) = -Real.log (512 / 709) := by
    rw [show ((709 / 512) : ℝ) = ((512 / 709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (242875993 / 500000000) ≤ -Real.log (315 / 512) ∧
    -Real.log (315 / 512) ≤ (485751987 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 827)) (n := 12)
    (lo := (242875993 / 500000000)) (hi := (485751987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 315) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 315) = 1/(315 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-485751987 / 1000000000) (-242875993 / 500000000) (Real.log (315 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (2031923 / 6250000) ≤ -Real.log (5120 / 7087) ∧
    -Real.log (5120 / 7087) ≤ (325107681 / 1000000000) := by
  have h := checkLog_sound (w := (1967 / 12207)) (n := 12)
    (lo := (2031923 / 6250000)) (hi := (325107681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7087 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7087 / 5120) = 1/(5120 / 7087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (2031923 / 6250000) (325107681 / 1000000000) (Real.log (7087 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7087 / 5120) = -Real.log (5120 / 7087) := by
    rw [show ((7087 / 5120) : ℝ) = ((5120 / 7087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (242400029 / 500000000) ≤ -Real.log (3153 / 5120) ∧
    -Real.log (3153 / 5120) ≤ (484800059 / 1000000000) := by
  have h := checkLog_sound (w := (1967 / 8273)) (n := 12)
    (lo := (242400029 / 500000000)) (hi := (484800059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3153) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3153) = 1/(3153 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-484800059 / 1000000000) (-242400029 / 500000000) (Real.log (3153 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (30214943 / 125000000) ≤ -Real.log (1000000 / 1273437) ∧
    -Real.log (1000000 / 1273437) ≤ (48343909 / 200000000) := by
  have h := checkLog_sound (w := (273437 / 2273437)) (n := 12)
    (lo := (30214943 / 125000000)) (hi := (48343909 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1273437 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1273437 / 1000000) = 1/(1000000 / 1273437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (30214943 / 125000000) (48343909 / 200000000) (Real.log (1273437 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1273437 / 1000000) = -Real.log (1000000 / 1273437) := by
    rw [show ((1273437 / 1000000) : ℝ) = ((1000000 / 1273437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (159715041 / 500000000) ≤ -Real.log (726563 / 1000000) ∧
    -Real.log (726563 / 1000000) ≤ (319430083 / 1000000000) := by
  have h := checkLog_sound (w := (273437 / 1726563)) (n := 12)
    (lo := (159715041 / 500000000)) (hi := (319430083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 726563) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 726563) = 1/(726563 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-319430083 / 1000000000) (-159715041 / 500000000) (Real.log (726563 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (121026223 / 500000000) ≤ -Real.log (1000000 / 1273861) ∧
    -Real.log (1000000 / 1273861) ≤ (242052447 / 1000000000) := by
  have h := checkLog_sound (w := (273861 / 2273861)) (n := 12)
    (lo := (121026223 / 500000000)) (hi := (242052447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1273861 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1273861 / 1000000) = 1/(1000000 / 1273861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (121026223 / 500000000) (242052447 / 1000000000) (Real.log (1273861 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1273861 / 1000000) = -Real.log (1000000 / 1273861) := by
    rw [show ((1273861 / 1000000) : ℝ) = ((1000000 / 1273861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (160006911 / 500000000) ≤ -Real.log (726139 / 1000000) ∧
    -Real.log (726139 / 1000000) ≤ (320013823 / 1000000000) := by
  have h := checkLog_sound (w := (273861 / 1726139)) (n := 12)
    (lo := (160006911 / 500000000)) (hi := (320013823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 726139) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 726139) = 1/(726139 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-320013823 / 1000000000) (-160006911 / 500000000) (Real.log (726139 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (90092137 / 500000000) ≤ -Real.log (500000 / 598719) ∧
    -Real.log (500000 / 598719) ≤ (7207371 / 40000000) := by
  have h := checkLog_sound (w := (98719 / 1098719)) (n := 12)
    (lo := (90092137 / 500000000)) (hi := (7207371 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((598719 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(598719 / 500000) = 1/(500000 / 598719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (90092137 / 500000000) (7207371 / 40000000) (Real.log (598719 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (598719 / 500000) = -Real.log (500000 / 598719) := by
    rw [show ((598719 / 500000) : ℝ) = ((500000 / 598719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (27493271 / 125000000) ≤ -Real.log (401281 / 500000) ∧
    -Real.log (401281 / 500000) ≤ (219946169 / 1000000000) := by
  have h := checkLog_sound (w := (98719 / 901281)) (n := 12)
    (lo := (27493271 / 125000000)) (hi := (219946169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 401281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 401281) = 1/(401281 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-219946169 / 1000000000) (-27493271 / 125000000) (Real.log (401281 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (180450641 / 1000000000) ≤ -Real.log (1000000 / 1197757) ∧
    -Real.log (1000000 / 1197757) ≤ (90225321 / 500000000) := by
  have h := checkLog_sound (w := (197757 / 2197757)) (n := 12)
    (lo := (180450641 / 1000000000)) (hi := (90225321 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1197757 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1197757 / 1000000) = 1/(1000000 / 1197757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (180450641 / 1000000000) (90225321 / 500000000) (Real.log (1197757 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1197757 / 1000000) = -Real.log (1000000 / 1197757) := by
    rw [show ((1197757 / 1000000) : ℝ) = ((1000000 / 1197757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (55085931 / 250000000) ≤ -Real.log (802243 / 1000000) ∧
    -Real.log (802243 / 1000000) ≤ (8813749 / 40000000) := by
  have h := checkLog_sound (w := (197757 / 1802243)) (n := 12)
    (lo := (55085931 / 250000000)) (hi := (8813749 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 802243) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 802243) = 1/(802243 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-8813749 / 40000000) (-55085931 / 250000000) (Real.log (802243 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (404953869 / 500000000) ≤ -Real.log (5000000000 / 11238503013) ∧
    -Real.log (5000000000 / 11238503013) ≤ (40495387 / 50000000) := by
  have h := checkLog_sound (w := (1238503013 / 21238503013)) (n := 12)
    (lo := (58380279 / 500000000)) (hi := (116760559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11238503013 / 10000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(11238503013 / 10000000000) = 1/(5000000000 / 11238503013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (404953869 / 500000000) (40495387 / 50000000) (Real.log (11238503013 / 5000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (11238503013 / 5000000000) = -Real.log (5000000000 / 11238503013) := by
    rw [show ((11238503013 / 5000000000) : ℝ) = ((5000000000 / 11238503013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (811282887 / 1000000000) ≤ -Real.log (500000000000 / 1125396825397) ∧
    -Real.log (500000000000 / 1125396825397) ≤ (811282889 / 1000000000) := by
  have h := checkLog_sound (w := (125396825397 / 2125396825397)) (n := 12)
    (lo := (118135707 / 1000000000)) (hi := (29533927 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1125396825397 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1125396825397 / 1000000000000) = 1/(500000000000 / 1125396825397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (811282887 / 1000000000) (811282889 / 1000000000) (Real.log (1125396825397 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1125396825397 / 500000000000) = -Real.log (500000000000 / 1125396825397) := by
    rw [show ((1125396825397 / 500000000000) : ℝ) = ((500000000000 / 1125396825397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (280574813 / 500000000) ≤ -Real.log (25000000000 / 43817156943) ∧
    -Real.log (25000000000 / 43817156943) ≤ (561149627 / 1000000000) := by
  have h := checkLog_sound (w := (18817156943 / 68817156943)) (n := 12)
    (lo := (280574813 / 500000000)) (hi := (561149627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43817156943 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43817156943 / 25000000000) = 1/(25000000000 / 43817156943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (280574813 / 500000000) (561149627 / 1000000000) (Real.log (43817156943 / 25000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (43817156943 / 25000000000) = -Real.log (25000000000 / 43817156943) := by
    rw [show ((43817156943 / 25000000000) : ℝ) = ((25000000000 / 43817156943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (140516567 / 250000000) ≤ -Real.log (250000000000 / 438573399859) ∧
    -Real.log (250000000000 / 438573399859) ≤ (562066269 / 1000000000) := by
  have h := checkLog_sound (w := (188573399859 / 688573399859)) (n := 12)
    (lo := (140516567 / 250000000)) (hi := (562066269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((438573399859 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(438573399859 / 250000000000) = 1/(250000000000 / 438573399859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (140516567 / 250000000) (562066269 / 1000000000) (Real.log (438573399859 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (438573399859 / 250000000000) = -Real.log (250000000000 / 438573399859) := by
    rw [show ((438573399859 / 250000000000) : ℝ) = ((250000000000 / 438573399859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (200065221 / 500000000) ≤ -Real.log (250000000000 / 373004827041) ∧
    -Real.log (250000000000 / 373004827041) ≤ (400130443 / 1000000000) := by
  have h := checkLog_sound (w := (123004827041 / 623004827041)) (n := 12)
    (lo := (200065221 / 500000000)) (hi := (400130443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((373004827041 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(373004827041 / 250000000000) = 1/(250000000000 / 373004827041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (200065221 / 500000000) (400130443 / 1000000000) (Real.log (373004827041 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (373004827041 / 250000000000) = -Real.log (250000000000 / 373004827041) := by
    rw [show ((373004827041 / 250000000000) : ℝ) = ((250000000000 / 373004827041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (80158873 / 200000000) ≤ -Real.log (100000000000 / 149301022259) ∧
    -Real.log (100000000000 / 149301022259) ≤ (200397183 / 500000000) := by
  have h := checkLog_sound (w := (49301022259 / 249301022259)) (n := 12)
    (lo := (80158873 / 200000000)) (hi := (200397183 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149301022259 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149301022259 / 100000000000) = 1/(100000000000 / 149301022259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (80158873 / 200000000) (200397183 / 500000000) (Real.log (149301022259 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (149301022259 / 100000000000) = -Real.log (100000000000 / 149301022259) := by
    rw [show ((149301022259 / 100000000000) : ℝ) = ((100000000000 / 149301022259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (39893083 / 1000000000) ≤ -Real.log (960892168951 / 1000000000000) ∧
    -Real.log (960892168951 / 1000000000000) ≤ (9973271 / 250000000) := by
  have h := checkLog_sound (w := (39107831049 / 1960892168951)) (n := 12)
    (lo := (39893083 / 1000000000)) (hi := (9973271 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 960892168951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 960892168951) = 1/(960892168951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-9973271 / 250000000) (-39893083 / 1000000000) (Real.log (960892168951 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (39761893 / 1000000000) ≤ -Real.log (240254559039 / 250000000000) ∧
    -Real.log (240254559039 / 250000000000) ≤ (19880947 / 500000000) := by
  have h := checkLog_sound (w := (9745440961 / 490254559039)) (n := 12)
    (lo := (39761893 / 1000000000)) (hi := (19880947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 240254559039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 240254559039) = 1/(240254559039 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-19880947 / 500000000) (-39761893 / 1000000000) (Real.log (240254559039 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell229

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell230Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell230
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

theorem reflection_log_1_neg : (325953943 / 1000000000) ≤ -Real.log (5120 / 7093) ∧
    -Real.log (5120 / 7093) ≤ (40744243 / 125000000) := by
  have h := checkLog_sound (w := (1973 / 12213)) (n := 12)
    (lo := (325953943 / 1000000000)) (hi := (40744243 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7093 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7093 / 5120) = 1/(5120 / 7093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (325953943 / 1000000000) (40744243 / 125000000) (Real.log (7093 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7093 / 5120) = -Real.log (5120 / 7093) := by
    rw [show ((7093 / 5120) : ℝ) = ((5120 / 7093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (24335241 / 50000000) ≤ -Real.log (3147 / 5120) ∧
    -Real.log (3147 / 5120) ≤ (486704821 / 1000000000) := by
  have h := checkLog_sound (w := (1973 / 8267)) (n := 12)
    (lo := (24335241 / 50000000)) (hi := (486704821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3147) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3147) = 1/(3147 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-486704821 / 1000000000) (-24335241 / 50000000) (Real.log (3147 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (325530901 / 1000000000) ≤ -Real.log (512 / 709) ∧
    -Real.log (512 / 709) ≤ (162765451 / 500000000) := by
  have h := checkLog_sound (w := (197 / 1221)) (n := 12)
    (lo := (325530901 / 1000000000)) (hi := (162765451 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((709 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(709 / 512) = 1/(512 / 709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (325530901 / 1000000000) (162765451 / 500000000) (Real.log (709 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (709 / 512) = -Real.log (512 / 709) := by
    rw [show ((709 / 512) : ℝ) = ((512 / 709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (242875993 / 500000000) ≤ -Real.log (315 / 512) ∧
    -Real.log (315 / 512) ≤ (485751987 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 827)) (n := 12)
    (lo := (242875993 / 500000000)) (hi := (485751987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 315) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 315) = 1/(315 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-485751987 / 1000000000) (-242875993 / 500000000) (Real.log (315 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (242051661 / 1000000000) ≤ -Real.log (50000 / 63693) ∧
    -Real.log (50000 / 63693) ≤ (121025831 / 500000000) := by
  have h := checkLog_sound (w := (13693 / 113693)) (n := 12)
    (lo := (242051661 / 1000000000)) (hi := (121025831 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((63693 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(63693 / 50000) = 1/(50000 / 63693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (242051661 / 1000000000) (121025831 / 500000000) (Real.log (63693 / 50000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (63693 / 50000) = -Real.log (50000 / 63693) := by
    rw [show ((63693 / 50000) : ℝ) = ((50000 / 63693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (64002489 / 200000000) ≤ -Real.log (36307 / 50000) ∧
    -Real.log (36307 / 50000) ≤ (160006223 / 500000000) := by
  have h := checkLog_sound (w := (13693 / 86307)) (n := 12)
    (lo := (64002489 / 200000000)) (hi := (160006223 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 36307) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 36307) = 1/(36307 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-160006223 / 500000000) (-64002489 / 200000000) (Real.log (36307 / 50000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (60596113 / 250000000) ≤ -Real.log (250000 / 318571) ∧
    -Real.log (250000 / 318571) ≤ (242384453 / 1000000000) := by
  have h := checkLog_sound (w := (68571 / 568571)) (n := 12)
    (lo := (60596113 / 250000000)) (hi := (242384453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((318571 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(318571 / 250000) = 1/(250000 / 318571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (60596113 / 250000000) (242384453 / 1000000000) (Real.log (318571 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (318571 / 250000) = -Real.log (250000 / 318571) := by
    rw [show ((318571 / 250000) : ℝ) = ((250000 / 318571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (12823861 / 40000000) ≤ -Real.log (181429 / 250000) ∧
    -Real.log (181429 / 250000) ≤ (160298263 / 500000000) := by
  have h := checkLog_sound (w := (68571 / 431429)) (n := 12)
    (lo := (12823861 / 40000000)) (hi := (160298263 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 181429) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 181429) = 1/(181429 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-160298263 / 500000000) (-12823861 / 40000000) (Real.log (181429 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (90224903 / 500000000) ≤ -Real.log (250000 / 299439) ∧
    -Real.log (250000 / 299439) ≤ (180449807 / 1000000000) := by
  have h := checkLog_sound (w := (49439 / 549439)) (n := 12)
    (lo := (90224903 / 500000000)) (hi := (180449807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299439 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299439 / 250000) = 1/(250000 / 299439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (90224903 / 500000000) (180449807 / 1000000000) (Real.log (299439 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (299439 / 250000) = -Real.log (250000 / 299439) := by
    rw [show ((299439 / 250000) : ℝ) = ((250000 / 299439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (220342477 / 1000000000) ≤ -Real.log (200561 / 250000) ∧
    -Real.log (200561 / 250000) ≤ (110171239 / 500000000) := by
  have h := checkLog_sound (w := (49439 / 450561)) (n := 12)
    (lo := (220342477 / 1000000000)) (hi := (110171239 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 200561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 200561) = 1/(200561 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-110171239 / 500000000) (-220342477 / 1000000000) (Real.log (200561 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (90358051 / 500000000) ≤ -Real.log (40000 / 47923) ∧
    -Real.log (40000 / 47923) ≤ (180716103 / 1000000000) := by
  have h := checkLog_sound (w := (7923 / 87923)) (n := 12)
    (lo := (90358051 / 500000000)) (hi := (180716103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47923 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(47923 / 40000) = 1/(40000 / 47923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (90358051 / 500000000) (180716103 / 1000000000) (Real.log (47923 / 40000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (47923 / 40000) = -Real.log (40000 / 47923) := by
    rw [show ((47923 / 40000) : ℝ) = ((40000 / 47923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (220740191 / 1000000000) ≤ -Real.log (32077 / 40000) ∧
    -Real.log (32077 / 40000) ≤ (6898131 / 31250000) := by
  have h := checkLog_sound (w := (7923 / 72077)) (n := 12)
    (lo := (220740191 / 1000000000)) (hi := (6898131 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 32077) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 32077) = 1/(32077 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-6898131 / 31250000) (-220740191 / 1000000000) (Real.log (32077 / 40000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (811282887 / 1000000000) ≤ -Real.log (125000000000 / 281349206349) ∧
    -Real.log (125000000000 / 281349206349) ≤ (811282889 / 1000000000) := by
  have h := checkLog_sound (w := (31349206349 / 531349206349)) (n := 12)
    (lo := (118135707 / 1000000000)) (hi := (29533927 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((281349206349 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(281349206349 / 250000000000) = 1/(125000000000 / 281349206349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (811282887 / 1000000000) (811282889 / 1000000000) (Real.log (281349206349 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (281349206349 / 125000000000) = -Real.log (125000000000 / 281349206349) := by
    rw [show ((281349206349 / 125000000000) : ℝ) = ((125000000000 / 281349206349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (812658763 / 1000000000) ≤ -Real.log (250000000000 / 563473149031) ∧
    -Real.log (250000000000 / 563473149031) ≤ (162531753 / 200000000) := by
  have h := checkLog_sound (w := (63473149031 / 1063473149031)) (n := 12)
    (lo := (119511583 / 1000000000)) (hi := (3734737 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((563473149031 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(563473149031 / 500000000000) = 1/(250000000000 / 563473149031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (812658763 / 1000000000) (162531753 / 200000000) (Real.log (563473149031 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (563473149031 / 250000000000) = -Real.log (250000000000 / 563473149031) := by
    rw [show ((563473149031 / 250000000000) : ℝ) = ((250000000000 / 563473149031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (281032053 / 500000000) ≤ -Real.log (250000000000 / 438572451593) ∧
    -Real.log (250000000000 / 438572451593) ≤ (562064107 / 1000000000) := by
  have h := checkLog_sound (w := (188572451593 / 688572451593)) (n := 12)
    (lo := (281032053 / 500000000)) (hi := (562064107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((438572451593 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(438572451593 / 250000000000) = 1/(250000000000 / 438572451593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (281032053 / 500000000) (562064107 / 1000000000) (Real.log (438572451593 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (438572451593 / 250000000000) = -Real.log (250000000000 / 438572451593) := by
    rw [show ((438572451593 / 250000000000) : ℝ) = ((250000000000 / 438572451593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (562980977 / 1000000000) ≤ -Real.log (500000000000 / 877949500907) ∧
    -Real.log (500000000000 / 877949500907) ≤ (281490489 / 500000000) := by
  have h := checkLog_sound (w := (377949500907 / 1377949500907)) (n := 12)
    (lo := (562980977 / 1000000000)) (hi := (281490489 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((877949500907 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(877949500907 / 500000000000) = 1/(500000000000 / 877949500907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (562980977 / 1000000000) (281490489 / 500000000) (Real.log (877949500907 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (877949500907 / 500000000000) = -Real.log (500000000000 / 877949500907) := by
    rw [show ((877949500907 / 500000000000) : ℝ) = ((500000000000 / 877949500907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (100198071 / 250000000) ≤ -Real.log (500000000000 / 746503557521) ∧
    -Real.log (500000000000 / 746503557521) ≤ (80158457 / 200000000) := by
  have h := checkLog_sound (w := (246503557521 / 1246503557521)) (n := 12)
    (lo := (100198071 / 250000000)) (hi := (80158457 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((746503557521 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(746503557521 / 500000000000) = 1/(500000000000 / 746503557521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (100198071 / 250000000) (80158457 / 200000000) (Real.log (746503557521 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (746503557521 / 500000000000) = -Real.log (500000000000 / 746503557521) := by
    rw [show ((746503557521 / 500000000000) : ℝ) = ((500000000000 / 746503557521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (401456293 / 1000000000) ≤ -Real.log (125000000000 / 186749851919) ∧
    -Real.log (125000000000 / 186749851919) ≤ (200728147 / 500000000) := by
  have h := checkLog_sound (w := (61749851919 / 311749851919)) (n := 12)
    (lo := (401456293 / 1000000000)) (hi := (200728147 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((186749851919 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(186749851919 / 125000000000) = 1/(125000000000 / 186749851919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (401456293 / 1000000000) (200728147 / 500000000) (Real.log (186749851919 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (186749851919 / 125000000000) = -Real.log (125000000000 / 186749851919) := by
    rw [show ((186749851919 / 125000000000) : ℝ) = ((125000000000 / 186749851919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (40024089 / 1000000000) ≤ -Real.log (1537226071 / 1600000000) ∧
    -Real.log (1537226071 / 1600000000) ≤ (4002409 / 100000000) := by
  have h := checkLog_sound (w := (62773929 / 3137226071)) (n := 12)
    (lo := (40024089 / 1000000000)) (hi := (4002409 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1537226071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1537226071) = 1/(1537226071 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-4002409 / 100000000) (-40024089 / 1000000000) (Real.log (1537226071 / 1600000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (39892671 / 1000000000) ≤ -Real.log (60055785279 / 62500000000) ∧
    -Real.log (60055785279 / 62500000000) ≤ (623323 / 15625000) := by
  have h := checkLog_sound (w := (2444214721 / 122555785279)) (n := 12)
    (lo := (39892671 / 1000000000)) (hi := (623323 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60055785279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60055785279) = 1/(60055785279 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-623323 / 15625000) (-39892671 / 1000000000) (Real.log (60055785279 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell230

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell231Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell231
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

theorem reflection_log_1_neg : (65275361 / 200000000) ≤ -Real.log (640 / 887) ∧
    -Real.log (640 / 887) ≤ (163188403 / 500000000) := by
  have h := checkLog_sound (w := (247 / 1527)) (n := 12)
    (lo := (65275361 / 200000000)) (hi := (163188403 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((887 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(887 / 640) = 1/(640 / 887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (65275361 / 200000000) (163188403 / 500000000) (Real.log (887 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (887 / 640) = -Real.log (640 / 887) := by
    rw [show ((887 / 640) : ℝ) = ((640 / 887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (121914641 / 250000000) ≤ -Real.log (393 / 640) ∧
    -Real.log (393 / 640) ≤ (97531713 / 200000000) := by
  have h := checkLog_sound (w := (247 / 1033)) (n := 12)
    (lo := (121914641 / 250000000)) (hi := (97531713 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 393) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 393) = 1/(393 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-97531713 / 200000000) (-121914641 / 250000000) (Real.log (393 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (325953943 / 1000000000) ≤ -Real.log (5120 / 7093) ∧
    -Real.log (5120 / 7093) ≤ (40744243 / 125000000) := by
  have h := checkLog_sound (w := (1973 / 12213)) (n := 12)
    (lo := (325953943 / 1000000000)) (hi := (40744243 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7093 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7093 / 5120) = 1/(5120 / 7093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (325953943 / 1000000000) (40744243 / 125000000) (Real.log (7093 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7093 / 5120) = -Real.log (5120 / 7093) := by
    rw [show ((7093 / 5120) : ℝ) = ((5120 / 7093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (24335241 / 50000000) ≤ -Real.log (3147 / 5120) ∧
    -Real.log (3147 / 5120) ≤ (486704821 / 1000000000) := by
  have h := checkLog_sound (w := (1973 / 8267)) (n := 12)
    (lo := (24335241 / 50000000)) (hi := (486704821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3147) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3147) = 1/(3147 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-486704821 / 1000000000) (-24335241 / 50000000) (Real.log (3147 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (242383667 / 1000000000) ≤ -Real.log (1000000 / 1274283) ∧
    -Real.log (1000000 / 1274283) ≤ (60595917 / 250000000) := by
  have h := checkLog_sound (w := (274283 / 2274283)) (n := 12)
    (lo := (242383667 / 1000000000)) (hi := (60595917 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1274283 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1274283 / 1000000) = 1/(1000000 / 1274283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (242383667 / 1000000000) (60595917 / 250000000) (Real.log (1274283 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1274283 / 1000000) = -Real.log (1000000 / 1274283) := by
    rw [show ((1274283 / 1000000) : ℝ) = ((1000000 / 1274283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (320595147 / 1000000000) ≤ -Real.log (725717 / 1000000) ∧
    -Real.log (725717 / 1000000) ≤ (80148787 / 250000000) := by
  have h := checkLog_sound (w := (274283 / 1725717)) (n := 12)
    (lo := (320595147 / 1000000000)) (hi := (80148787 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 725717) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 725717) = 1/(725717 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-80148787 / 250000000) (-320595147 / 1000000000) (Real.log (725717 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (60679087 / 250000000) ≤ -Real.log (1000000 / 1274707) ∧
    -Real.log (1000000 / 1274707) ≤ (242716349 / 1000000000) := by
  have h := checkLog_sound (w := (274707 / 2274707)) (n := 12)
    (lo := (60679087 / 250000000)) (hi := (242716349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1274707 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1274707 / 1000000) = 1/(1000000 / 1274707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (60679087 / 250000000) (242716349 / 1000000000) (Real.log (1274707 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1274707 / 1000000) = -Real.log (1000000 / 1274707) := by
    rw [show ((1274707 / 1000000) : ℝ) = ((1000000 / 1274707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (321179567 / 1000000000) ≤ -Real.log (725293 / 1000000) ∧
    -Real.log (725293 / 1000000) ≤ (20073723 / 62500000) := by
  have h := checkLog_sound (w := (274707 / 1725293)) (n := 12)
    (lo := (321179567 / 1000000000)) (hi := (20073723 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 725293) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 725293) = 1/(725293 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-20073723 / 62500000) (-321179567 / 1000000000) (Real.log (725293 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (180715267 / 1000000000) ≤ -Real.log (500000 / 599037) ∧
    -Real.log (500000 / 599037) ≤ (45178817 / 250000000) := by
  have h := checkLog_sound (w := (99037 / 1099037)) (n := 12)
    (lo := (180715267 / 1000000000)) (hi := (45178817 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((599037 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(599037 / 500000) = 1/(500000 / 599037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (180715267 / 1000000000) (45178817 / 250000000) (Real.log (599037 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (599037 / 500000) = -Real.log (500000 / 599037) := by
    rw [show ((599037 / 500000) : ℝ) = ((500000 / 599037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1724523 / 7812500) ≤ -Real.log (400963 / 500000) ∧
    -Real.log (400963 / 500000) ≤ (44147789 / 200000000) := by
  have h := checkLog_sound (w := (99037 / 900963)) (n := 12)
    (lo := (1724523 / 7812500)) (hi := (44147789 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 400963) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 400963) = 1/(400963 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-44147789 / 200000000) (-1724523 / 7812500) (Real.log (400963 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (180982327 / 1000000000) ≤ -Real.log (500000 / 599197) ∧
    -Real.log (500000 / 599197) ≤ (22622791 / 125000000) := by
  have h := checkLog_sound (w := (99197 / 1099197)) (n := 12)
    (lo := (180982327 / 1000000000)) (hi := (22622791 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((599197 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(599197 / 500000) = 1/(500000 / 599197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (180982327 / 1000000000) (22622791 / 125000000) (Real.log (599197 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (599197 / 500000) = -Real.log (500000 / 599197) := by
    rw [show ((599197 / 500000) : ℝ) = ((500000 / 599197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (221138063 / 1000000000) ≤ -Real.log (400803 / 500000) ∧
    -Real.log (400803 / 500000) ≤ (13821129 / 62500000) := by
  have h := checkLog_sound (w := (99197 / 900803)) (n := 12)
    (lo := (221138063 / 1000000000)) (hi := (13821129 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 400803) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 400803) = 1/(400803 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-13821129 / 62500000) (-221138063 / 1000000000) (Real.log (400803 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (812658763 / 1000000000) ≤ -Real.log (500000000000 / 1126946298061) ∧
    -Real.log (500000000000 / 1126946298061) ≤ (162531753 / 200000000) := by
  have h := checkLog_sound (w := (126946298061 / 2126946298061)) (n := 12)
    (lo := (119511583 / 1000000000)) (hi := (3734737 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1126946298061 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1126946298061 / 1000000000000) = 1/(500000000000 / 1126946298061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (812658763 / 1000000000) (162531753 / 200000000) (Real.log (1126946298061 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1126946298061 / 500000000000) = -Real.log (500000000000 / 1126946298061) := by
    rw [show ((1126946298061 / 500000000000) : ℝ) = ((500000000000 / 1126946298061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (814035369 / 1000000000) ≤ -Real.log (62500000000 / 141062340967) ∧
    -Real.log (62500000000 / 141062340967) ≤ (814035371 / 1000000000) := by
  have h := checkLog_sound (w := (16062340967 / 266062340967)) (n := 12)
    (lo := (120888189 / 1000000000)) (hi := (12088819 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((141062340967 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(141062340967 / 125000000000) = 1/(62500000000 / 141062340967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (814035369 / 1000000000) (814035371 / 1000000000) (Real.log (141062340967 / 62500000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (141062340967 / 62500000000) = -Real.log (62500000000 / 141062340967) := by
    rw [show ((141062340967 / 62500000000) : ℝ) = ((62500000000 / 141062340967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (281489407 / 500000000) ≤ -Real.log (125000000000 / 219486900541) ∧
    -Real.log (125000000000 / 219486900541) ≤ (112595763 / 200000000) := by
  have h := checkLog_sound (w := (94486900541 / 344486900541)) (n := 12)
    (lo := (281489407 / 500000000)) (hi := (112595763 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((219486900541 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(219486900541 / 125000000000) = 1/(125000000000 / 219486900541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (281489407 / 500000000) (112595763 / 200000000) (Real.log (219486900541 / 125000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (219486900541 / 125000000000) = -Real.log (125000000000 / 219486900541) := by
    rw [show ((219486900541 / 125000000000) : ℝ) = ((125000000000 / 219486900541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (140973979 / 250000000) ≤ -Real.log (500000000000 / 878753138387) ∧
    -Real.log (500000000000 / 878753138387) ≤ (563895917 / 1000000000) := by
  have h := checkLog_sound (w := (378753138387 / 1378753138387)) (n := 12)
    (lo := (140973979 / 250000000)) (hi := (563895917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((878753138387 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(878753138387 / 500000000000) = 1/(500000000000 / 878753138387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (140973979 / 250000000) (563895917 / 1000000000) (Real.log (878753138387 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (878753138387 / 500000000000) = -Real.log (500000000000 / 878753138387) := by
    rw [show ((878753138387 / 500000000000) : ℝ) = ((500000000000 / 878753138387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (100363553 / 250000000) ≤ -Real.log (500000000000 / 746997852669) ∧
    -Real.log (500000000000 / 746997852669) ≤ (401454213 / 1000000000) := by
  have h := checkLog_sound (w := (246997852669 / 1246997852669)) (n := 12)
    (lo := (100363553 / 250000000)) (hi := (401454213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((746997852669 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(746997852669 / 500000000000) = 1/(500000000000 / 746997852669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (100363553 / 250000000) (401454213 / 1000000000) (Real.log (746997852669 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (746997852669 / 500000000000) = -Real.log (500000000000 / 746997852669) := by
    rw [show ((746997852669 / 500000000000) : ℝ) = ((500000000000 / 746997852669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (40212039 / 100000000) ≤ -Real.log (250000000000 / 373747826239) ∧
    -Real.log (250000000000 / 373747826239) ≤ (402120391 / 1000000000) := by
  have h := checkLog_sound (w := (123747826239 / 623747826239)) (n := 12)
    (lo := (40212039 / 100000000)) (hi := (402120391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((373747826239 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(373747826239 / 250000000000) = 1/(250000000000 / 373747826239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (40212039 / 100000000) (402120391 / 1000000000) (Real.log (373747826239 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (373747826239 / 250000000000) = -Real.log (250000000000 / 373747826239) := by
    rw [show ((373747826239 / 250000000000) : ℝ) = ((250000000000 / 373747826239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (5019467 / 125000000) ≤ -Real.log (240159955191 / 250000000000) ∧
    -Real.log (240159955191 / 250000000000) ≤ (40155737 / 1000000000) := by
  have h := checkLog_sound (w := (9840044809 / 490159955191)) (n := 12)
    (lo := (5019467 / 125000000)) (hi := (40155737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 240159955191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 240159955191) = 1/(240159955191 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-40155737 / 1000000000) (-5019467 / 125000000) (Real.log (240159955191 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (40023677 / 1000000000) ≤ -Real.log (240191672631 / 250000000000) ∧
    -Real.log (240191672631 / 250000000000) ≤ (20011839 / 500000000) := by
  have h := checkLog_sound (w := (9808327369 / 490191672631)) (n := 12)
    (lo := (40023677 / 1000000000)) (hi := (20011839 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 240191672631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 240191672631) = 1/(240191672631 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-20011839 / 500000000) (-40023677 / 1000000000) (Real.log (240191672631 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell231

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell232Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell232
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

theorem reflection_log_1_neg : (32679949 / 100000000) ≤ -Real.log (5120 / 7099) ∧
    -Real.log (5120 / 7099) ≤ (326799491 / 1000000000) := by
  have h := checkLog_sound (w := (1979 / 12219)) (n := 12)
    (lo := (32679949 / 100000000)) (hi := (326799491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7099 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7099 / 5120) = 1/(5120 / 7099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (32679949 / 100000000) (326799491 / 1000000000) (Real.log (7099 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7099 / 5120) = -Real.log (5120 / 7099) := by
    rw [show ((7099 / 5120) : ℝ) = ((5120 / 7099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (244306609 / 500000000) ≤ -Real.log (3141 / 5120) ∧
    -Real.log (3141 / 5120) ≤ (488613219 / 1000000000) := by
  have h := checkLog_sound (w := (1979 / 8261)) (n := 12)
    (lo := (244306609 / 500000000)) (hi := (488613219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3141) = 1/(3141 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-488613219 / 1000000000) (-244306609 / 500000000) (Real.log (3141 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (65275361 / 200000000) ≤ -Real.log (640 / 887) ∧
    -Real.log (640 / 887) ≤ (163188403 / 500000000) := by
  have h := checkLog_sound (w := (247 / 1527)) (n := 12)
    (lo := (65275361 / 200000000)) (hi := (163188403 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((887 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(887 / 640) = 1/(640 / 887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (65275361 / 200000000) (163188403 / 500000000) (Real.log (887 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (887 / 640) = -Real.log (640 / 887) := by
    rw [show ((887 / 640) : ℝ) = ((640 / 887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (121914641 / 250000000) ≤ -Real.log (393 / 640) ∧
    -Real.log (393 / 640) ≤ (97531713 / 200000000) := by
  have h := checkLog_sound (w := (247 / 1033)) (n := 12)
    (lo := (121914641 / 250000000)) (hi := (97531713 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 393) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 393) = 1/(393 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-97531713 / 200000000) (-121914641 / 250000000) (Real.log (393 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (242715563 / 1000000000) ≤ -Real.log (500000 / 637353) ∧
    -Real.log (500000 / 637353) ≤ (60678891 / 250000000) := by
  have h := checkLog_sound (w := (137353 / 1137353)) (n := 12)
    (lo := (242715563 / 1000000000)) (hi := (60678891 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((637353 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(637353 / 500000) = 1/(500000 / 637353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (242715563 / 1000000000) (60678891 / 250000000) (Real.log (637353 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (637353 / 500000) = -Real.log (500000 / 637353) := by
    rw [show ((637353 / 500000) : ℝ) = ((500000 / 637353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (321178189 / 1000000000) ≤ -Real.log (362647 / 500000) ∧
    -Real.log (362647 / 500000) ≤ (32117819 / 100000000) := by
  have h := checkLog_sound (w := (137353 / 862647)) (n := 12)
    (lo := (321178189 / 1000000000)) (hi := (32117819 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 362647) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 362647) = 1/(362647 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-32117819 / 100000000) (-321178189 / 1000000000) (Real.log (362647 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (121524067 / 500000000) ≤ -Real.log (100000 / 127513) ∧
    -Real.log (100000 / 127513) ≤ (48609627 / 200000000) := by
  have h := checkLog_sound (w := (27513 / 227513)) (n := 12)
    (lo := (121524067 / 500000000)) (hi := (48609627 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((127513 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(127513 / 100000) = 1/(100000 / 127513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (121524067 / 500000000) (48609627 / 200000000) (Real.log (127513 / 100000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (127513 / 100000) = -Real.log (100000 / 127513) := by
    rw [show ((127513 / 100000) : ℝ) = ((100000 / 127513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (6435259 / 20000000) ≤ -Real.log (72487 / 100000) ∧
    -Real.log (72487 / 100000) ≤ (321762951 / 1000000000) := by
  have h := checkLog_sound (w := (27513 / 172487)) (n := 12)
    (lo := (6435259 / 20000000)) (hi := (321762951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 72487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 72487) = 1/(72487 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-321762951 / 1000000000) (-6435259 / 20000000) (Real.log (72487 / 100000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (45245373 / 250000000) ≤ -Real.log (1000000 / 1198393) ∧
    -Real.log (1000000 / 1198393) ≤ (180981493 / 1000000000) := by
  have h := checkLog_sound (w := (198393 / 2198393)) (n := 12)
    (lo := (45245373 / 250000000)) (hi := (180981493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1198393 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1198393 / 1000000) = 1/(1000000 / 1198393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (45245373 / 250000000) (180981493 / 1000000000) (Real.log (1198393 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1198393 / 1000000) = -Real.log (1000000 / 1198393) := by
    rw [show ((1198393 / 1000000) : ℝ) = ((1000000 / 1198393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (13821051 / 62500000) ≤ -Real.log (801607 / 1000000) ∧
    -Real.log (801607 / 1000000) ≤ (221136817 / 1000000000) := by
  have h := checkLog_sound (w := (198393 / 1801607)) (n := 12)
    (lo := (13821051 / 62500000)) (hi := (221136817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 801607) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 801607) = 1/(801607 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-221136817 / 1000000000) (-13821051 / 62500000) (Real.log (801607 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (181247647 / 1000000000) ≤ -Real.log (125000 / 149839) ∧
    -Real.log (125000 / 149839) ≤ (5663989 / 31250000) := by
  have h := checkLog_sound (w := (24839 / 274839)) (n := 12)
    (lo := (181247647 / 1000000000)) (hi := (5663989 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149839 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149839 / 125000) = 1/(125000 / 149839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (181247647 / 1000000000) (5663989 / 31250000) (Real.log (149839 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (149839 / 125000) = -Real.log (125000 / 149839) := by
    rw [show ((149839 / 125000) : ℝ) = ((125000 / 149839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (44306969 / 200000000) ≤ -Real.log (100161 / 125000) ∧
    -Real.log (100161 / 125000) ≤ (110767423 / 500000000) := by
  have h := checkLog_sound (w := (24839 / 225161)) (n := 12)
    (lo := (44306969 / 200000000)) (hi := (110767423 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 100161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 100161) = 1/(100161 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-110767423 / 500000000) (-44306969 / 200000000) (Real.log (100161 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (814035369 / 1000000000) ≤ -Real.log (100000000000 / 225699745547) ∧
    -Real.log (100000000000 / 225699745547) ≤ (814035371 / 1000000000) := by
  have h := checkLog_sound (w := (25699745547 / 425699745547)) (n := 12)
    (lo := (120888189 / 1000000000)) (hi := (12088819 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((225699745547 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(225699745547 / 200000000000) = 1/(100000000000 / 225699745547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (814035369 / 1000000000) (814035371 / 1000000000) (Real.log (225699745547 / 100000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (225699745547 / 100000000000) = -Real.log (100000000000 / 225699745547) := by
    rw [show ((225699745547 / 100000000000) : ℝ) = ((100000000000 / 225699745547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (815412707 / 1000000000) ≤ -Real.log (500000000000 / 1130054122891) ∧
    -Real.log (500000000000 / 1130054122891) ≤ (815412709 / 1000000000) := by
  have h := checkLog_sound (w := (130054122891 / 2130054122891)) (n := 12)
    (lo := (122265527 / 1000000000)) (hi := (15283191 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1130054122891 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1130054122891 / 1000000000000) = 1/(500000000000 / 1130054122891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (815412707 / 1000000000) (815412709 / 1000000000) (Real.log (1130054122891 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1130054122891 / 500000000000) = -Real.log (500000000000 / 1130054122891) := by
    rw [show ((1130054122891 / 500000000000) : ℝ) = ((500000000000 / 1130054122891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (70486719 / 125000000) ≤ -Real.log (500000000000 / 878751237429) ∧
    -Real.log (500000000000 / 878751237429) ≤ (563893753 / 1000000000) := by
  have h := checkLog_sound (w := (378751237429 / 1378751237429)) (n := 12)
    (lo := (70486719 / 125000000)) (hi := (563893753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((878751237429 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(878751237429 / 500000000000) = 1/(500000000000 / 878751237429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (70486719 / 125000000) (563893753 / 1000000000) (Real.log (878751237429 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (878751237429 / 500000000000) = -Real.log (500000000000 / 878751237429) := by
    rw [show ((878751237429 / 500000000000) : ℝ) = ((500000000000 / 878751237429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (141202771 / 250000000) ≤ -Real.log (500000000000 / 879557713797) ∧
    -Real.log (500000000000 / 879557713797) ≤ (112962217 / 200000000) := by
  have h := checkLog_sound (w := (379557713797 / 1379557713797)) (n := 12)
    (lo := (141202771 / 250000000)) (hi := (112962217 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((879557713797 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(879557713797 / 500000000000) = 1/(500000000000 / 879557713797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (141202771 / 250000000) (112962217 / 200000000) (Real.log (879557713797 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (879557713797 / 500000000000) = -Real.log (500000000000 / 879557713797) := by
    rw [show ((879557713797 / 500000000000) : ℝ) = ((500000000000 / 879557713797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (100529577 / 250000000) ≤ -Real.log (250000000000 / 373747048117) ∧
    -Real.log (250000000000 / 373747048117) ≤ (402118309 / 1000000000) := by
  have h := checkLog_sound (w := (123747048117 / 623747048117)) (n := 12)
    (lo := (100529577 / 250000000)) (hi := (402118309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((373747048117 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(373747048117 / 250000000000) = 1/(250000000000 / 373747048117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (100529577 / 250000000) (402118309 / 1000000000) (Real.log (373747048117 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (373747048117 / 250000000000) = -Real.log (250000000000 / 373747048117) := by
    rw [show ((373747048117 / 250000000000) : ℝ) = ((250000000000 / 373747048117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (402782493 / 1000000000) ≤ -Real.log (500000000000 / 747990734917) ∧
    -Real.log (500000000000 / 747990734917) ≤ (201391247 / 500000000) := by
  have h := checkLog_sound (w := (247990734917 / 1247990734917)) (n := 12)
    (lo := (402782493 / 1000000000)) (hi := (201391247 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((747990734917 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(747990734917 / 500000000000) = 1/(500000000000 / 747990734917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (402782493 / 1000000000) (201391247 / 500000000) (Real.log (747990734917 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (747990734917 / 500000000000) = -Real.log (500000000000 / 747990734917) := by
    rw [show ((747990734917 / 500000000000) : ℝ) = ((500000000000 / 747990734917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (20143599 / 500000000) ≤ -Real.log (15008024079 / 15625000000) ∧
    -Real.log (15008024079 / 15625000000) ≤ (40287199 / 1000000000) := by
  have h := checkLog_sound (w := (616975921 / 30633024079)) (n := 12)
    (lo := (20143599 / 500000000)) (hi := (40287199 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15008024079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15008024079) = 1/(15008024079 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-40287199 / 1000000000) (-20143599 / 500000000) (Real.log (15008024079 / 15625000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (40155323 / 1000000000) ≤ -Real.log (960640217551 / 1000000000000) ∧
    -Real.log (960640217551 / 1000000000000) ≤ (10038831 / 250000000) := by
  have h := checkLog_sound (w := (39359782449 / 1960640217551)) (n := 12)
    (lo := (40155323 / 1000000000)) (hi := (10038831 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 960640217551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 960640217551) = 1/(960640217551 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-10038831 / 250000000) (-40155323 / 1000000000) (Real.log (960640217551 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell232

end


