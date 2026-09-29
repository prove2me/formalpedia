-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0051__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0051__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T21:50:38.937873+00:00
-- url     : https://prove2.me/theorems/90bd3036-7d14-4ef3-8b58-effc13200690
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0051 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0052, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0051 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0052, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0053)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0051 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0052, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0053)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0051 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0052, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0053) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0051 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0052, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0053).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0051 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_3264_neg : (34723 / 200000000) ≤ -Real.log (1249783 / 1250000) ∧
    -Real.log (1249783 / 1250000) ≤ (10851 / 62500000) := by
  have h := checkLog_sound (w := (217 / 2499783)) (n := 12)
    (lo := (34723 / 200000000)) (hi := (10851 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1249783) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1249783) = 1/(1249783 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3264 : Bounds (-10851 / 62500000) (-34723 / 200000000) (Real.log (1249783 / 1250000)) := by
  have h := reflection_log_3264_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3265_neg : (16709711 / 200000000) ≤ -Real.log (500000 / 543569) ∧
    -Real.log (500000 / 543569) ≤ (20887139 / 250000000) := by
  have h := checkLog_sound (w := (43569 / 1043569)) (n := 12)
    (lo := (16709711 / 200000000)) (hi := (20887139 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((543569 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(543569 / 500000) = 1/(500000 / 543569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3265 : Bounds (16709711 / 200000000) (20887139 / 250000000) (Real.log (543569 / 500000)) := by
  have h := reflection_log_3265_neg
  have he : Real.log (543569 / 500000) = -Real.log (500000 / 543569) := by
    rw [show ((543569 / 500000) : ℝ) = ((500000 / 543569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3266_neg : (91170559 / 1000000000) ≤ -Real.log (456431 / 500000) ∧
    -Real.log (456431 / 500000) ≤ (71227 / 781250) := by
  have h := checkLog_sound (w := (43569 / 956431)) (n := 12)
    (lo := (91170559 / 1000000000)) (hi := (71227 / 781250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 456431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 456431) = 1/(456431 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3266 : Bounds (-71227 / 781250) (-91170559 / 1000000000) (Real.log (456431 / 500000)) := by
  have h := reflection_log_3266_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3267_neg : (83755499 / 1000000000) ≤ -Real.log (1000000 / 1087363) ∧
    -Real.log (1000000 / 1087363) ≤ (167511 / 2000000) := by
  have h := checkLog_sound (w := (87363 / 2087363)) (n := 12)
    (lo := (83755499 / 1000000000)) (hi := (167511 / 2000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1087363 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1087363 / 1000000) = 1/(1000000 / 1087363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3267 : Bounds (83755499 / 1000000000) (167511 / 2000000) (Real.log (1087363 / 1000000)) := by
  have h := reflection_log_3267_neg
  have he : Real.log (1087363 / 1000000) = -Real.log (1000000 / 1087363) := by
    rw [show ((1087363 / 1000000) : ℝ) = ((1000000 / 1087363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3268_neg : (91417067 / 1000000000) ≤ -Real.log (912637 / 1000000) ∧
    -Real.log (912637 / 1000000) ≤ (22854267 / 250000000) := by
  have h := checkLog_sound (w := (87363 / 1912637)) (n := 12)
    (lo := (91417067 / 1000000000)) (hi := (22854267 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 912637) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 912637) = 1/(912637 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3268 : Bounds (-22854267 / 250000000) (-91417067 / 1000000000) (Real.log (912637 / 1000000)) := by
  have h := reflection_log_3268_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3269_neg : (14964 / 1953125) ≤ -Real.log (992367706231 / 1000000000000) ∧
    -Real.log (992367706231 / 1000000000000) ≤ (7661569 / 1000000000) := by
  have h := checkLog_sound (w := (7632293769 / 1992367706231)) (n := 12)
    (lo := (14964 / 1953125)) (hi := (7661569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992367706231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992367706231) = 1/(992367706231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3269 : Bounds (-7661569 / 1000000000) (-14964 / 1953125) (Real.log (992367706231 / 1000000000000)) := by
  have h := reflection_log_3269_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3270_neg : (1905501 / 250000000) ≤ -Real.log (248101742239 / 250000000000) ∧
    -Real.log (248101742239 / 250000000000) ≤ (1524401 / 200000000) := by
  have h := checkLog_sound (w := (1898257761 / 498101742239)) (n := 12)
    (lo := (1905501 / 250000000)) (hi := (1524401 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248101742239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248101742239) = 1/(248101742239 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3270 : Bounds (-1524401 / 200000000) (-1905501 / 250000000) (Real.log (248101742239 / 250000000000)) := by
  have h := reflection_log_3270_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3271_neg : (87359557 / 500000000) ≤ -Real.log (4000000000 / 4763646641) ∧
    -Real.log (4000000000 / 4763646641) ≤ (34943823 / 200000000) := by
  have h := checkLog_sound (w := (763646641 / 8763646641)) (n := 12)
    (lo := (87359557 / 500000000)) (hi := (34943823 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4763646641 / 4000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4763646641 / 4000000000) = 1/(4000000000 / 4763646641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3271 : Bounds (87359557 / 500000000) (34943823 / 200000000) (Real.log (4763646641 / 4000000000)) := by
  have h := reflection_log_3271_neg
  have he : Real.log (4763646641 / 4000000000) = -Real.log (4000000000 / 4763646641) := by
    rw [show ((4763646641 / 4000000000) : ℝ) = ((4000000000 / 4763646641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3272_neg : (87586283 / 500000000) ≤ -Real.log (20000000000 / 23829036079) ∧
    -Real.log (20000000000 / 23829036079) ≤ (175172567 / 1000000000) := by
  have h := checkLog_sound (w := (3829036079 / 43829036079)) (n := 12)
    (lo := (87586283 / 500000000)) (hi := (175172567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23829036079 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23829036079 / 20000000000) = 1/(20000000000 / 23829036079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3272 : Bounds (87586283 / 500000000) (175172567 / 1000000000) (Real.log (23829036079 / 20000000000)) := by
  have h := reflection_log_3272_neg
  have he : Real.log (23829036079 / 20000000000) = -Real.log (20000000000 / 23829036079) := by
    rw [show ((23829036079 / 20000000000) : ℝ) = ((20000000000 / 23829036079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3273_neg : (175273049 / 500000000) ≤ -Real.log (500000000000 / 709921355111) ∧
    -Real.log (500000000000 / 709921355111) ≤ (350546099 / 1000000000) := by
  have h := checkLog_sound (w := (209921355111 / 1209921355111)) (n := 12)
    (lo := (175273049 / 500000000)) (hi := (350546099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((709921355111 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(709921355111 / 500000000000) = 1/(500000000000 / 709921355111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3273 : Bounds (175273049 / 500000000) (350546099 / 1000000000) (Real.log (709921355111 / 500000000000)) := by
  have h := reflection_log_3273_neg
  have he : Real.log (709921355111 / 500000000000) = -Real.log (500000000000 / 709921355111) := by
    rw [show ((709921355111 / 500000000000) : ℝ) = ((500000000000 / 709921355111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3274_neg : (350752309 / 1000000000) ≤ -Real.log (100000000000 / 142013552759) ∧
    -Real.log (100000000000 / 142013552759) ≤ (35075231 / 100000000) := by
  have h := checkLog_sound (w := (42013552759 / 242013552759)) (n := 12)
    (lo := (350752309 / 1000000000)) (hi := (35075231 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142013552759 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(142013552759 / 100000000000) = 1/(100000000000 / 142013552759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3274 : Bounds (350752309 / 1000000000) (35075231 / 100000000) (Real.log (142013552759 / 100000000000)) := by
  have h := reflection_log_3274_neg
  have he : Real.log (142013552759 / 100000000000) = -Real.log (100000000000 / 142013552759) := by
    rw [show ((142013552759 / 100000000000) : ℝ) = ((100000000000 / 142013552759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3275_neg : (1251259 / 7812500) ≤ -Real.log (10000 / 11737) ∧
    -Real.log (10000 / 11737) ≤ (160161153 / 1000000000) := by
  have h := checkLog_sound (w := (1737 / 21737)) (n := 12)
    (lo := (1251259 / 7812500)) (hi := (160161153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11737 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11737 / 10000) = 1/(10000 / 11737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3275 : Bounds (1251259 / 7812500) (160161153 / 1000000000) (Real.log (11737 / 10000)) := by
  have h := reflection_log_3275_neg
  have he : Real.log (11737 / 10000) = -Real.log (10000 / 11737) := by
    rw [show ((11737 / 10000) : ℝ) = ((10000 / 11737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3276_neg : (1526379 / 8000000) ≤ -Real.log (8263 / 10000) ∧
    -Real.log (8263 / 10000) ≤ (2981209 / 15625000) := by
  have h := checkLog_sound (w := (1737 / 18263)) (n := 12)
    (lo := (1526379 / 8000000)) (hi := (2981209 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8263) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8263) = 1/(8263 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3276 : Bounds (-2981209 / 15625000) (-1526379 / 8000000) (Real.log (8263 / 10000)) := by
  have h := reflection_log_3276_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3277_neg : (43421 / 250000000) ≤ -Real.log (10000000 / 10001737) ∧
    -Real.log (10000000 / 10001737) ≤ (34737 / 200000000) := by
  have h := checkLog_sound (w := (1737 / 20001737)) (n := 12)
    (lo := (43421 / 250000000)) (hi := (34737 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001737 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001737 / 10000000) = 1/(10000000 / 10001737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3277 : Bounds (43421 / 250000000) (34737 / 200000000) (Real.log (10001737 / 10000000)) := by
  have h := reflection_log_3277_neg
  have he : Real.log (10001737 / 10000000) = -Real.log (10000000 / 10001737) := by
    rw [show ((10001737 / 10000000) : ℝ) = ((10000000 / 10001737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3278_neg : (34743 / 200000000) ≤ -Real.log (9998263 / 10000000) ∧
    -Real.log (9998263 / 10000000) ≤ (43429 / 250000000) := by
  have h := checkLog_sound (w := (1737 / 19998263)) (n := 12)
    (lo := (34743 / 200000000)) (hi := (43429 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998263) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998263) = 1/(9998263 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3278 : Bounds (-43429 / 250000000) (-34743 / 200000000) (Real.log (9998263 / 10000000)) := by
  have h := reflection_log_3278_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3279_neg : (41797733 / 500000000) ≤ -Real.log (1000000 / 1087189) ∧
    -Real.log (1000000 / 1087189) ≤ (83595467 / 1000000000) := by
  have h := checkLog_sound (w := (87189 / 2087189)) (n := 12)
    (lo := (41797733 / 500000000)) (hi := (83595467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1087189 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1087189 / 1000000) = 1/(1000000 / 1087189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3279 : Bounds (41797733 / 500000000) (83595467 / 1000000000) (Real.log (1087189 / 1000000)) := by
  have h := reflection_log_3279_neg
  have he : Real.log (1087189 / 1000000) = -Real.log (1000000 / 1087189) := by
    rw [show ((1087189 / 1000000) : ℝ) = ((1000000 / 1087189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3280_neg : (91226429 / 1000000000) ≤ -Real.log (912811 / 1000000) ∧
    -Real.log (912811 / 1000000) ≤ (9122643 / 100000000) := by
  have h := checkLog_sound (w := (87189 / 1912811)) (n := 12)
    (lo := (91226429 / 1000000000)) (hi := (9122643 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 912811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 912811) = 1/(912811 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3280 : Bounds (-9122643 / 100000000) (-91226429 / 1000000000) (Real.log (912811 / 1000000)) := by
  have h := reflection_log_3280_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3281_neg : (104753 / 1250000) ≤ -Real.log (500000 / 543707) ∧
    -Real.log (500000 / 543707) ≤ (83802401 / 1000000000) := by
  have h := checkLog_sound (w := (43707 / 1043707)) (n := 12)
    (lo := (104753 / 1250000)) (hi := (83802401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((543707 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(543707 / 500000) = 1/(500000 / 543707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3281 : Bounds (104753 / 1250000) (83802401 / 1000000000) (Real.log (543707 / 500000)) := by
  have h := reflection_log_3281_neg
  have he : Real.log (543707 / 500000) = -Real.log (500000 / 543707) := by
    rw [show ((543707 / 500000) : ℝ) = ((500000 / 543707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3282_neg : (91472951 / 1000000000) ≤ -Real.log (456293 / 500000) ∧
    -Real.log (456293 / 500000) ≤ (11434119 / 125000000) := by
  have h := checkLog_sound (w := (43707 / 956293)) (n := 12)
    (lo := (91472951 / 1000000000)) (hi := (11434119 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 456293) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 456293) = 1/(456293 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3282 : Bounds (-11434119 / 125000000) (-91472951 / 1000000000) (Real.log (456293 / 500000)) := by
  have h := reflection_log_3282_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3283_neg : (153411 / 20000000) ≤ -Real.log (248089698151 / 250000000000) ∧
    -Real.log (248089698151 / 250000000000) ≤ (7670551 / 1000000000) := by
  have h := checkLog_sound (w := (1910301849 / 498089698151)) (n := 12)
    (lo := (153411 / 20000000)) (hi := (7670551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248089698151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248089698151) = 1/(248089698151 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3283 : Bounds (-7670551 / 1000000000) (-153411 / 20000000) (Real.log (248089698151 / 250000000000)) := by
  have h := reflection_log_3283_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3284_neg : (7630963 / 1000000000) ≤ -Real.log (992398078279 / 1000000000000) ∧
    -Real.log (992398078279 / 1000000000000) ≤ (1907741 / 250000000) := by
  have h := checkLog_sound (w := (7601921721 / 1992398078279)) (n := 12)
    (lo := (7630963 / 1000000000)) (hi := (1907741 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992398078279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992398078279) = 1/(992398078279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3284 : Bounds (-1907741 / 250000000) (-7630963 / 1000000000) (Real.log (992398078279 / 1000000000000)) := by
  have h := reflection_log_3284_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3285_neg : (34964379 / 200000000) ≤ -Real.log (250000000000 / 297758517371) ∧
    -Real.log (250000000000 / 297758517371) ≤ (21852737 / 125000000) := by
  have h := checkLog_sound (w := (47758517371 / 547758517371)) (n := 12)
    (lo := (34964379 / 200000000)) (hi := (21852737 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297758517371 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297758517371 / 250000000000) = 1/(250000000000 / 297758517371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3285 : Bounds (34964379 / 200000000) (21852737 / 125000000) (Real.log (297758517371 / 250000000000)) := by
  have h := reflection_log_3285_neg
  have he : Real.log (297758517371 / 250000000000) = -Real.log (250000000000 / 297758517371) := by
    rw [show ((297758517371 / 250000000000) : ℝ) = ((250000000000 / 297758517371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3286_neg : (175275351 / 1000000000) ≤ -Real.log (250000000000 / 297893568387) ∧
    -Real.log (250000000000 / 297893568387) ≤ (21909419 / 125000000) := by
  have h := checkLog_sound (w := (47893568387 / 547893568387)) (n := 12)
    (lo := (175275351 / 1000000000)) (hi := (21909419 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297893568387 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297893568387 / 250000000000) = 1/(250000000000 / 297893568387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3286 : Bounds (175275351 / 1000000000) (21909419 / 125000000) (Real.log (297893568387 / 250000000000)) := by
  have h := reflection_log_3286_neg
  have he : Real.log (297893568387 / 250000000000) = -Real.log (250000000000 / 297893568387) := by
    rw [show ((297893568387 / 250000000000) : ℝ) = ((250000000000 / 297893568387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3287_neg : (350752309 / 1000000000) ≤ -Real.log (250000000000 / 355033881897) ∧
    -Real.log (250000000000 / 355033881897) ≤ (35075231 / 100000000) := by
  have h := checkLog_sound (w := (105033881897 / 605033881897)) (n := 12)
    (lo := (350752309 / 1000000000)) (hi := (35075231 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((355033881897 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(355033881897 / 250000000000) = 1/(250000000000 / 355033881897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3287 : Bounds (350752309 / 1000000000) (35075231 / 100000000) (Real.log (355033881897 / 250000000000)) := by
  have h := reflection_log_3287_neg
  have he : Real.log (355033881897 / 250000000000) = -Real.log (250000000000 / 355033881897) := by
    rw [show ((355033881897 / 250000000000) : ℝ) = ((250000000000 / 355033881897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3288_neg : (350958527 / 1000000000) ≤ -Real.log (100000000000 / 142042841583) ∧
    -Real.log (100000000000 / 142042841583) ≤ (5483727 / 15625000) := by
  have h := checkLog_sound (w := (42042841583 / 242042841583)) (n := 12)
    (lo := (350958527 / 1000000000)) (hi := (5483727 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142042841583 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(142042841583 / 100000000000) = 1/(100000000000 / 142042841583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3288 : Bounds (350958527 / 1000000000) (5483727 / 15625000) (Real.log (142042841583 / 100000000000)) := by
  have h := reflection_log_3288_neg
  have he : Real.log (142042841583 / 100000000000) = -Real.log (100000000000 / 142042841583) := by
    rw [show ((142042841583 / 100000000000) : ℝ) = ((100000000000 / 142042841583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3289_neg : (160246349 / 1000000000) ≤ -Real.log (5000 / 5869) ∧
    -Real.log (5000 / 5869) ≤ (3204927 / 20000000) := by
  have h := checkLog_sound (w := (869 / 10869)) (n := 12)
    (lo := (160246349 / 1000000000)) (hi := (3204927 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5869 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5869 / 5000) = 1/(5000 / 5869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3289 : Bounds (160246349 / 1000000000) (3204927 / 20000000) (Real.log (5869 / 5000)) := by
  have h := reflection_log_3289_neg
  have he : Real.log (5869 / 5000) = -Real.log (5000 / 5869) := by
    rw [show ((5869 / 5000) : ℝ) = ((5000 / 5869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3290_neg : (47729601 / 250000000) ≤ -Real.log (4131 / 5000) ∧
    -Real.log (4131 / 5000) ≤ (38183681 / 200000000) := by
  have h := checkLog_sound (w := (869 / 9131)) (n := 12)
    (lo := (47729601 / 250000000)) (hi := (38183681 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4131) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4131) = 1/(4131 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3290 : Bounds (-38183681 / 200000000) (-47729601 / 250000000) (Real.log (4131 / 5000)) := by
  have h := reflection_log_3290_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3291_neg : (21723 / 125000000) ≤ -Real.log (5000000 / 5000869) ∧
    -Real.log (5000000 / 5000869) ≤ (34757 / 200000000) := by
  have h := checkLog_sound (w := (869 / 10000869)) (n := 12)
    (lo := (21723 / 125000000)) (hi := (34757 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000869 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000869 / 5000000) = 1/(5000000 / 5000869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3291 : Bounds (21723 / 125000000) (34757 / 200000000) (Real.log (5000869 / 5000000)) := by
  have h := reflection_log_3291_neg
  have he : Real.log (5000869 / 5000000) = -Real.log (5000000 / 5000869) := by
    rw [show ((5000869 / 5000000) : ℝ) = ((5000000 / 5000869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3292_neg : (34763 / 200000000) ≤ -Real.log (4999131 / 5000000) ∧
    -Real.log (4999131 / 5000000) ≤ (21727 / 125000000) := by
  have h := checkLog_sound (w := (869 / 9999131)) (n := 12)
    (lo := (34763 / 200000000)) (hi := (21727 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999131) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999131) = 1/(4999131 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3292 : Bounds (-21727 / 125000000) (-34763 / 200000000) (Real.log (4999131 / 5000000)) := by
  have h := reflection_log_3292_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3293_neg : (41821187 / 500000000) ≤ -Real.log (25000 / 27181) ∧
    -Real.log (25000 / 27181) ≤ (669139 / 8000000) := by
  have h := checkLog_sound (w := (2181 / 52181)) (n := 12)
    (lo := (41821187 / 500000000)) (hi := (669139 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27181 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27181 / 25000) = 1/(25000 / 27181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3293 : Bounds (41821187 / 500000000) (669139 / 8000000) (Real.log (27181 / 25000)) := by
  have h := reflection_log_3293_neg
  have he : Real.log (27181 / 25000) = -Real.log (25000 / 27181) := by
    rw [show ((27181 / 25000) : ℝ) = ((25000 / 27181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3294_neg : (45641151 / 500000000) ≤ -Real.log (22819 / 25000) ∧
    -Real.log (22819 / 25000) ≤ (91282303 / 1000000000) := by
  have h := checkLog_sound (w := (2181 / 47819)) (n := 12)
    (lo := (45641151 / 500000000)) (hi := (91282303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 22819) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 22819) = 1/(22819 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3294 : Bounds (-91282303 / 1000000000) (-45641151 / 500000000) (Real.log (22819 / 25000)) := by
  have h := reflection_log_3294_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3295_neg : (83849299 / 1000000000) ≤ -Real.log (200000 / 217493) ∧
    -Real.log (200000 / 217493) ≤ (838493 / 10000000) := by
  have h := checkLog_sound (w := (17493 / 417493)) (n := 12)
    (lo := (83849299 / 1000000000)) (hi := (838493 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((217493 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(217493 / 200000) = 1/(200000 / 217493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3295 : Bounds (83849299 / 1000000000) (838493 / 10000000) (Real.log (217493 / 200000)) := by
  have h := reflection_log_3295_neg
  have he : Real.log (217493 / 200000) = -Real.log (200000 / 217493) := by
    rw [show ((217493 / 200000) : ℝ) = ((200000 / 217493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3296_neg : (45764419 / 500000000) ≤ -Real.log (182507 / 200000) ∧
    -Real.log (182507 / 200000) ≤ (91528839 / 1000000000) := by
  have h := checkLog_sound (w := (17493 / 382507)) (n := 12)
    (lo := (45764419 / 500000000)) (hi := (91528839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 182507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 182507) = 1/(182507 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3296 : Bounds (-91528839 / 1000000000) (-45764419 / 500000000) (Real.log (182507 / 200000)) := by
  have h := reflection_log_3296_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3297_neg : (3839769 / 500000000) ≤ -Real.log (39693994951 / 40000000000) ∧
    -Real.log (39693994951 / 40000000000) ≤ (7679539 / 1000000000) := by
  have h := checkLog_sound (w := (306005049 / 79693994951)) (n := 12)
    (lo := (3839769 / 500000000)) (hi := (7679539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39693994951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39693994951) = 1/(39693994951 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3297 : Bounds (-7679539 / 1000000000) (-3839769 / 500000000) (Real.log (39693994951 / 40000000000)) := by
  have h := reflection_log_3297_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3298_neg : (7639927 / 1000000000) ≤ -Real.log (620243239 / 625000000) ∧
    -Real.log (620243239 / 625000000) ≤ (954991 / 125000000) := by
  have h := checkLog_sound (w := (4756761 / 1245243239)) (n := 12)
    (lo := (7639927 / 1000000000)) (hi := (954991 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 620243239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 620243239) = 1/(620243239 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3298 : Bounds (-954991 / 125000000) (-7639927 / 1000000000) (Real.log (620243239 / 625000000)) := by
  have h := reflection_log_3298_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3299_neg : (174924677 / 1000000000) ≤ -Real.log (250000000000 / 297789123099) ∧
    -Real.log (250000000000 / 297789123099) ≤ (87462339 / 500000000) := by
  have h := checkLog_sound (w := (47789123099 / 547789123099)) (n := 12)
    (lo := (174924677 / 1000000000)) (hi := (87462339 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297789123099 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297789123099 / 250000000000) = 1/(250000000000 / 297789123099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3299 : Bounds (174924677 / 1000000000) (87462339 / 500000000) (Real.log (297789123099 / 250000000000)) := by
  have h := reflection_log_3299_neg
  have he : Real.log (297789123099 / 250000000000) = -Real.log (250000000000 / 297789123099) := by
    rw [show ((297789123099 / 250000000000) : ℝ) = ((250000000000 / 297789123099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3300_neg : (175378137 / 1000000000) ≤ -Real.log (500000000000 / 595848378419) ∧
    -Real.log (500000000000 / 595848378419) ≤ (87689069 / 500000000) := by
  have h := checkLog_sound (w := (95848378419 / 1095848378419)) (n := 12)
    (lo := (175378137 / 1000000000)) (hi := (87689069 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((595848378419 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(595848378419 / 500000000000) = 1/(500000000000 / 595848378419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3300 : Bounds (175378137 / 1000000000) (87689069 / 500000000) (Real.log (595848378419 / 500000000000)) := by
  have h := reflection_log_3300_neg
  have he : Real.log (595848378419 / 500000000000) = -Real.log (500000000000 / 595848378419) := by
    rw [show ((595848378419 / 500000000000) : ℝ) = ((500000000000 / 595848378419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3301_neg : (350958527 / 1000000000) ≤ -Real.log (250000000000 / 355107103957) ∧
    -Real.log (250000000000 / 355107103957) ≤ (5483727 / 15625000) := by
  have h := checkLog_sound (w := (105107103957 / 605107103957)) (n := 12)
    (lo := (350958527 / 1000000000)) (hi := (5483727 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((355107103957 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(355107103957 / 250000000000) = 1/(250000000000 / 355107103957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3301 : Bounds (350958527 / 1000000000) (5483727 / 15625000) (Real.log (355107103957 / 250000000000)) := by
  have h := reflection_log_3301_neg
  have he : Real.log (355107103957 / 250000000000) = -Real.log (250000000000 / 355107103957) := by
    rw [show ((355107103957 / 250000000000) : ℝ) = ((250000000000 / 355107103957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3302_neg : (351164753 / 1000000000) ≤ -Real.log (100000000000 / 142072137497) ∧
    -Real.log (100000000000 / 142072137497) ≤ (175582377 / 500000000) := by
  have h := checkLog_sound (w := (42072137497 / 242072137497)) (n := 12)
    (lo := (351164753 / 1000000000)) (hi := (175582377 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142072137497 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(142072137497 / 100000000000) = 1/(100000000000 / 142072137497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3302 : Bounds (351164753 / 1000000000) (175582377 / 500000000) (Real.log (142072137497 / 100000000000)) := by
  have h := reflection_log_3302_neg
  have he : Real.log (142072137497 / 100000000000) = -Real.log (100000000000 / 142072137497) := by
    rw [show ((142072137497 / 100000000000) : ℝ) = ((100000000000 / 142072137497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3303_neg : (80165769 / 500000000) ≤ -Real.log (10000 / 11739) ∧
    -Real.log (10000 / 11739) ≤ (160331539 / 1000000000) := by
  have h := checkLog_sound (w := (1739 / 21739)) (n := 12)
    (lo := (80165769 / 500000000)) (hi := (160331539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11739 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11739 / 10000) = 1/(10000 / 11739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3303 : Bounds (80165769 / 500000000) (160331539 / 1000000000) (Real.log (11739 / 10000)) := by
  have h := reflection_log_3303_neg
  have he : Real.log (11739 / 10000) = -Real.log (10000 / 11739) := by
    rw [show ((11739 / 10000) : ℝ) = ((10000 / 11739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3304_neg : (191039447 / 1000000000) ≤ -Real.log (8261 / 10000) ∧
    -Real.log (8261 / 10000) ≤ (23879931 / 125000000) := by
  have h := checkLog_sound (w := (1739 / 18261)) (n := 12)
    (lo := (191039447 / 1000000000)) (hi := (23879931 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8261) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8261) = 1/(8261 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3304 : Bounds (-23879931 / 125000000) (-191039447 / 1000000000) (Real.log (8261 / 10000)) := by
  have h := reflection_log_3304_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3305_neg : (43471 / 250000000) ≤ -Real.log (10000000 / 10001739) ∧
    -Real.log (10000000 / 10001739) ≤ (34777 / 200000000) := by
  have h := checkLog_sound (w := (1739 / 20001739)) (n := 12)
    (lo := (43471 / 250000000)) (hi := (34777 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001739 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001739 / 10000000) = 1/(10000000 / 10001739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3305 : Bounds (43471 / 250000000) (34777 / 200000000) (Real.log (10001739 / 10000000)) := by
  have h := reflection_log_3305_neg
  have he : Real.log (10001739 / 10000000) = -Real.log (10000000 / 10001739) := by
    rw [show ((10001739 / 10000000) : ℝ) = ((10000000 / 10001739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3306_neg : (34783 / 200000000) ≤ -Real.log (9998261 / 10000000) ∧
    -Real.log (9998261 / 10000000) ≤ (43479 / 250000000) := by
  have h := checkLog_sound (w := (1739 / 19998261)) (n := 12)
    (lo := (34783 / 200000000)) (hi := (43479 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998261) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998261) = 1/(9998261 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3306 : Bounds (-43479 / 250000000) (-34783 / 200000000) (Real.log (9998261 / 10000000)) := by
  have h := reflection_log_3306_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3307_neg : (83689281 / 1000000000) ≤ -Real.log (1000000 / 1087291) ∧
    -Real.log (1000000 / 1087291) ≤ (41844641 / 500000000) := by
  have h := checkLog_sound (w := (87291 / 2087291)) (n := 12)
    (lo := (83689281 / 1000000000)) (hi := (41844641 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1087291 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1087291 / 1000000) = 1/(1000000 / 1087291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3307 : Bounds (83689281 / 1000000000) (41844641 / 500000000) (Real.log (1087291 / 1000000)) := by
  have h := reflection_log_3307_neg
  have he : Real.log (1087291 / 1000000) = -Real.log (1000000 / 1087291) := by
    rw [show ((1087291 / 1000000) : ℝ) = ((1000000 / 1087291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3308_neg : (45669089 / 500000000) ≤ -Real.log (912709 / 1000000) ∧
    -Real.log (912709 / 1000000) ≤ (91338179 / 1000000000) := by
  have h := checkLog_sound (w := (87291 / 1912709)) (n := 12)
    (lo := (45669089 / 500000000)) (hi := (91338179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 912709) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 912709) = 1/(912709 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3308 : Bounds (-91338179 / 1000000000) (-45669089 / 500000000) (Real.log (912709 / 1000000)) := by
  have h := reflection_log_3308_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3309_neg : (20973819 / 250000000) ≤ -Real.log (200000 / 217503) ∧
    -Real.log (200000 / 217503) ≤ (83895277 / 1000000000) := by
  have h := checkLog_sound (w := (17503 / 417503)) (n := 12)
    (lo := (20973819 / 250000000)) (hi := (83895277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((217503 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(217503 / 200000) = 1/(200000 / 217503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3309 : Bounds (20973819 / 250000000) (83895277 / 1000000000) (Real.log (217503 / 200000)) := by
  have h := reflection_log_3309_neg
  have he : Real.log (217503 / 200000) = -Real.log (200000 / 217503) := by
    rw [show ((217503 / 200000) : ℝ) = ((200000 / 217503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3310_neg : (5723977 / 62500000) ≤ -Real.log (182497 / 200000) ∧
    -Real.log (182497 / 200000) ≤ (91583633 / 1000000000) := by
  have h := checkLog_sound (w := (17503 / 382497)) (n := 12)
    (lo := (5723977 / 62500000)) (hi := (91583633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 182497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 182497) = 1/(182497 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3310 : Bounds (-91583633 / 1000000000) (-5723977 / 62500000) (Real.log (182497 / 200000)) := by
  have h := reflection_log_3310_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3311_neg : (1537671 / 200000000) ≤ -Real.log (39693644991 / 40000000000) ∧
    -Real.log (39693644991 / 40000000000) ≤ (1922089 / 250000000) := by
  have h := checkLog_sound (w := (306355009 / 79693644991)) (n := 12)
    (lo := (1537671 / 200000000)) (hi := (1922089 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39693644991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39693644991) = 1/(39693644991 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3311 : Bounds (-1922089 / 250000000) (-1537671 / 200000000) (Real.log (39693644991 / 40000000000)) := by
  have h := reflection_log_3311_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3312_neg : (7648897 / 1000000000) ≤ -Real.log (992380281319 / 1000000000000) ∧
    -Real.log (992380281319 / 1000000000000) ≤ (3824449 / 500000000) := by
  have h := checkLog_sound (w := (7619718681 / 1992380281319)) (n := 12)
    (lo := (7648897 / 1000000000)) (hi := (3824449 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992380281319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992380281319) = 1/(992380281319 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3312 : Bounds (-3824449 / 500000000) (-7648897 / 1000000000) (Real.log (992380281319 / 1000000000000)) := by
  have h := reflection_log_3312_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3313_neg : (8751373 / 50000000) ≤ -Real.log (100000000000 / 119127892899) ∧
    -Real.log (100000000000 / 119127892899) ≤ (175027461 / 1000000000) := by
  have h := checkLog_sound (w := (19127892899 / 219127892899)) (n := 12)
    (lo := (8751373 / 50000000)) (hi := (175027461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119127892899 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(119127892899 / 100000000000) = 1/(100000000000 / 119127892899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3313 : Bounds (8751373 / 50000000) (175027461 / 1000000000) (Real.log (119127892899 / 100000000000)) := by
  have h := reflection_log_3313_neg
  have he : Real.log (119127892899 / 100000000000) = -Real.log (100000000000 / 119127892899) := by
    rw [show ((119127892899 / 100000000000) : ℝ) = ((100000000000 / 119127892899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3314_neg : (175478909 / 1000000000) ≤ -Real.log (125000000000 / 148977106473) ∧
    -Real.log (125000000000 / 148977106473) ≤ (17547891 / 100000000) := by
  have h := checkLog_sound (w := (23977106473 / 273977106473)) (n := 12)
    (lo := (175478909 / 1000000000)) (hi := (17547891 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148977106473 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148977106473 / 125000000000) = 1/(125000000000 / 148977106473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3314 : Bounds (175478909 / 1000000000) (17547891 / 100000000) (Real.log (148977106473 / 125000000000)) := by
  have h := reflection_log_3314_neg
  have he : Real.log (148977106473 / 125000000000) = -Real.log (125000000000 / 148977106473) := by
    rw [show ((148977106473 / 125000000000) : ℝ) = ((125000000000 / 148977106473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3315_neg : (351164753 / 1000000000) ≤ -Real.log (125000000000 / 177590171871) ∧
    -Real.log (125000000000 / 177590171871) ≤ (175582377 / 500000000) := by
  have h := checkLog_sound (w := (52590171871 / 302590171871)) (n := 12)
    (lo := (351164753 / 1000000000)) (hi := (175582377 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((177590171871 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(177590171871 / 125000000000) = 1/(125000000000 / 177590171871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3315 : Bounds (351164753 / 1000000000) (175582377 / 500000000) (Real.log (177590171871 / 125000000000)) := by
  have h := reflection_log_3315_neg
  have he : Real.log (177590171871 / 125000000000) = -Real.log (125000000000 / 177590171871) := by
    rw [show ((177590171871 / 125000000000) : ℝ) = ((125000000000 / 177590171871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3316_neg : (175685493 / 500000000) ≤ -Real.log (250000000000 / 355253601259) ∧
    -Real.log (250000000000 / 355253601259) ≤ (351370987 / 1000000000) := by
  have h := checkLog_sound (w := (105253601259 / 605253601259)) (n := 12)
    (lo := (175685493 / 500000000)) (hi := (351370987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((355253601259 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(355253601259 / 250000000000) = 1/(250000000000 / 355253601259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3316 : Bounds (175685493 / 500000000) (351370987 / 1000000000) (Real.log (355253601259 / 250000000000)) := by
  have h := reflection_log_3316_neg
  have he : Real.log (355253601259 / 250000000000) = -Real.log (250000000000 / 355253601259) := by
    rw [show ((355253601259 / 250000000000) : ℝ) = ((250000000000 / 355253601259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3317_neg : (160416721 / 1000000000) ≤ -Real.log (500 / 587) ∧
    -Real.log (500 / 587) ≤ (80208361 / 500000000) := by
  have h := checkLog_sound (w := (87 / 1087)) (n := 12)
    (lo := (160416721 / 1000000000)) (hi := (80208361 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((587 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(587 / 500) = 1/(500 / 587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3317 : Bounds (160416721 / 1000000000) (80208361 / 500000000) (Real.log (587 / 500)) := by
  have h := reflection_log_3317_neg
  have he : Real.log (587 / 500) = -Real.log (500 / 587) := by
    rw [show ((587 / 500) : ℝ) = ((500 / 587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3318_neg : (38232101 / 200000000) ≤ -Real.log (413 / 500) ∧
    -Real.log (413 / 500) ≤ (95580253 / 500000000) := by
  have h := checkLog_sound (w := (87 / 913)) (n := 12)
    (lo := (38232101 / 200000000)) (hi := (95580253 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 413) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 413) = 1/(413 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3318 : Bounds (-95580253 / 500000000) (-38232101 / 200000000) (Real.log (413 / 500)) := by
  have h := reflection_log_3318_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3319_neg : (5437 / 31250000) ≤ -Real.log (500000 / 500087) ∧
    -Real.log (500000 / 500087) ≤ (34797 / 200000000) := by
  have h := checkLog_sound (w := (87 / 1000087)) (n := 12)
    (lo := (5437 / 31250000)) (hi := (34797 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500087 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500087 / 500000) = 1/(500000 / 500087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3319 : Bounds (5437 / 31250000) (34797 / 200000000) (Real.log (500087 / 500000)) := by
  have h := reflection_log_3319_neg
  have he : Real.log (500087 / 500000) = -Real.log (500000 / 500087) := by
    rw [show ((500087 / 500000) : ℝ) = ((500000 / 500087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3320_neg : (34803 / 200000000) ≤ -Real.log (499913 / 500000) ∧
    -Real.log (499913 / 500000) ≤ (2719 / 15625000) := by
  have h := checkLog_sound (w := (87 / 999913)) (n := 12)
    (lo := (34803 / 200000000)) (hi := (2719 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499913) = 1/(499913 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3320 : Bounds (-2719 / 15625000) (-34803 / 200000000) (Real.log (499913 / 500000)) := by
  have h := reflection_log_3320_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3321_neg : (41867633 / 500000000) ≤ -Real.log (1000000 / 1087341) ∧
    -Real.log (1000000 / 1087341) ≤ (83735267 / 1000000000) := by
  have h := checkLog_sound (w := (87341 / 2087341)) (n := 12)
    (lo := (41867633 / 500000000)) (hi := (83735267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1087341 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1087341 / 1000000) = 1/(1000000 / 1087341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3321 : Bounds (41867633 / 500000000) (83735267 / 1000000000) (Real.log (1087341 / 1000000)) := by
  have h := reflection_log_3321_neg
  have he : Real.log (1087341 / 1000000) = -Real.log (1000000 / 1087341) := by
    rw [show ((1087341 / 1000000) : ℝ) = ((1000000 / 1087341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3322_neg : (45696481 / 500000000) ≤ -Real.log (912659 / 1000000) ∧
    -Real.log (912659 / 1000000) ≤ (91392963 / 1000000000) := by
  have h := checkLog_sound (w := (87341 / 1912659)) (n := 12)
    (lo := (45696481 / 500000000)) (hi := (91392963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 912659) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 912659) = 1/(912659 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3322 : Bounds (-91392963 / 1000000000) (-45696481 / 500000000) (Real.log (912659 / 1000000)) := by
  have h := reflection_log_3322_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3323_neg : (83942171 / 1000000000) ≤ -Real.log (500000 / 543783) ∧
    -Real.log (500000 / 543783) ≤ (20985543 / 250000000) := by
  have h := checkLog_sound (w := (43783 / 1043783)) (n := 12)
    (lo := (83942171 / 1000000000)) (hi := (20985543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((543783 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(543783 / 500000) = 1/(500000 / 543783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3323 : Bounds (83942171 / 1000000000) (20985543 / 250000000) (Real.log (543783 / 500000)) := by
  have h := reflection_log_3323_neg
  have he : Real.log (543783 / 500000) = -Real.log (500000 / 543783) := by
    rw [show ((543783 / 500000) : ℝ) = ((500000 / 543783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3324_neg : (22909881 / 250000000) ≤ -Real.log (456217 / 500000) ∧
    -Real.log (456217 / 500000) ≤ (3665581 / 40000000) := by
  have h := checkLog_sound (w := (43783 / 956217)) (n := 12)
    (lo := (22909881 / 250000000)) (hi := (3665581 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 456217) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 456217) = 1/(456217 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3324 : Bounds (-3665581 / 40000000) (-22909881 / 250000000) (Real.log (456217 / 500000)) := by
  have h := reflection_log_3324_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3325_neg : (7697353 / 1000000000) ≤ -Real.log (248083048911 / 250000000000) ∧
    -Real.log (248083048911 / 250000000000) ≤ (3848677 / 500000000) := by
  have h := checkLog_sound (w := (1916951089 / 498083048911)) (n := 12)
    (lo := (7697353 / 1000000000)) (hi := (3848677 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248083048911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248083048911) = 1/(248083048911 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3325 : Bounds (-3848677 / 500000000) (-7697353 / 1000000000) (Real.log (248083048911 / 250000000000)) := by
  have h := reflection_log_3325_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3326_neg : (1531539 / 200000000) ≤ -Real.log (992371549719 / 1000000000000) ∧
    -Real.log (992371549719 / 1000000000000) ≤ (239303 / 31250000) := by
  have h := checkLog_sound (w := (7628450281 / 1992371549719)) (n := 12)
    (lo := (1531539 / 200000000)) (hi := (239303 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992371549719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992371549719) = 1/(992371549719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3326 : Bounds (-239303 / 31250000) (-1531539 / 200000000) (Real.log (992371549719 / 1000000000000)) := by
  have h := reflection_log_3326_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3327_neg : (43782057 / 250000000) ≤ -Real.log (20000000000 / 23827979563) ∧
    -Real.log (20000000000 / 23827979563) ≤ (175128229 / 1000000000) := by
  have h := checkLog_sound (w := (3827979563 / 43827979563)) (n := 12)
    (lo := (43782057 / 250000000)) (hi := (175128229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23827979563 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23827979563 / 20000000000) = 1/(20000000000 / 23827979563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3327 : Bounds (43782057 / 250000000) (175128229 / 1000000000) (Real.log (23827979563 / 20000000000)) := by
  have h := reflection_log_3327_neg
  have he : Real.log (23827979563 / 20000000000) = -Real.log (20000000000 / 23827979563) := by
    rw [show ((23827979563 / 20000000000) : ℝ) = ((20000000000 / 23827979563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0052 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_3328_neg : (342933 / 1953125) ≤ -Real.log (100000000000 / 119193936219) ∧
    -Real.log (100000000000 / 119193936219) ≤ (175581697 / 1000000000) := by
  have h := checkLog_sound (w := (19193936219 / 219193936219)) (n := 12)
    (lo := (342933 / 1953125)) (hi := (175581697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119193936219 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(119193936219 / 100000000000) = 1/(100000000000 / 119193936219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3328 : Bounds (342933 / 1953125) (175581697 / 1000000000) (Real.log (119193936219 / 100000000000)) := by
  have h := reflection_log_3328_neg
  have he : Real.log (119193936219 / 100000000000) = -Real.log (100000000000 / 119193936219) := by
    rw [show ((119193936219 / 100000000000) : ℝ) = ((100000000000 / 119193936219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3329_neg : (175685493 / 500000000) ≤ -Real.log (500000000000 / 710507202517) ∧
    -Real.log (500000000000 / 710507202517) ≤ (351370987 / 1000000000) := by
  have h := checkLog_sound (w := (210507202517 / 1210507202517)) (n := 12)
    (lo := (175685493 / 500000000)) (hi := (351370987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((710507202517 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(710507202517 / 500000000000) = 1/(500000000000 / 710507202517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3329 : Bounds (175685493 / 500000000) (351370987 / 1000000000) (Real.log (710507202517 / 500000000000)) := by
  have h := reflection_log_3329_neg
  have he : Real.log (710507202517 / 500000000000) = -Real.log (500000000000 / 710507202517) := by
    rw [show ((710507202517 / 500000000000) : ℝ) = ((500000000000 / 710507202517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3330_neg : (175788613 / 500000000) ≤ -Real.log (500000000000 / 710653753027) ∧
    -Real.log (500000000000 / 710653753027) ≤ (351577227 / 1000000000) := by
  have h := checkLog_sound (w := (210653753027 / 1210653753027)) (n := 12)
    (lo := (175788613 / 500000000)) (hi := (351577227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((710653753027 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(710653753027 / 500000000000) = 1/(500000000000 / 710653753027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3330 : Bounds (175788613 / 500000000) (351577227 / 1000000000) (Real.log (710653753027 / 500000000000)) := by
  have h := reflection_log_3330_neg
  have he : Real.log (710653753027 / 500000000000) = -Real.log (500000000000 / 710653753027) := by
    rw [show ((710653753027 / 500000000000) : ℝ) = ((500000000000 / 710653753027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3331_neg : (20062737 / 125000000) ≤ -Real.log (10000 / 11741) ∧
    -Real.log (10000 / 11741) ≤ (160501897 / 1000000000) := by
  have h := checkLog_sound (w := (1741 / 21741)) (n := 12)
    (lo := (20062737 / 125000000)) (hi := (160501897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11741 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11741 / 10000) = 1/(10000 / 11741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3331 : Bounds (20062737 / 125000000) (160501897 / 1000000000) (Real.log (11741 / 10000)) := by
  have h := reflection_log_3331_neg
  have he : Real.log (11741 / 10000) = -Real.log (10000 / 11741) := by
    rw [show ((11741 / 10000) : ℝ) = ((10000 / 11741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3332_neg : (95640789 / 500000000) ≤ -Real.log (8259 / 10000) ∧
    -Real.log (8259 / 10000) ≤ (191281579 / 1000000000) := by
  have h := checkLog_sound (w := (1741 / 18259)) (n := 12)
    (lo := (95640789 / 500000000)) (hi := (191281579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8259) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8259) = 1/(8259 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3332 : Bounds (-191281579 / 1000000000) (-95640789 / 500000000) (Real.log (8259 / 10000)) := by
  have h := reflection_log_3332_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3333_neg : (43521 / 250000000) ≤ -Real.log (10000000 / 10001741) ∧
    -Real.log (10000000 / 10001741) ≤ (34817 / 200000000) := by
  have h := checkLog_sound (w := (1741 / 20001741)) (n := 12)
    (lo := (43521 / 250000000)) (hi := (34817 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001741 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001741 / 10000000) = 1/(10000000 / 10001741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3333 : Bounds (43521 / 250000000) (34817 / 200000000) (Real.log (10001741 / 10000000)) := by
  have h := reflection_log_3333_neg
  have he : Real.log (10001741 / 10000000) = -Real.log (10000000 / 10001741) := by
    rw [show ((10001741 / 10000000) : ℝ) = ((10000000 / 10001741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3334_neg : (34823 / 200000000) ≤ -Real.log (9998259 / 10000000) ∧
    -Real.log (9998259 / 10000000) ≤ (43529 / 250000000) := by
  have h := checkLog_sound (w := (1741 / 19998259)) (n := 12)
    (lo := (34823 / 200000000)) (hi := (43529 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998259) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998259) = 1/(9998259 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3334 : Bounds (-43529 / 250000000) (-34823 / 200000000) (Real.log (9998259 / 10000000)) := by
  have h := reflection_log_3334_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3335_neg : (10472771 / 125000000) ≤ -Real.log (31250 / 33981) ∧
    -Real.log (31250 / 33981) ≤ (83782169 / 1000000000) := by
  have h := checkLog_sound (w := (2731 / 65231)) (n := 12)
    (lo := (10472771 / 125000000)) (hi := (83782169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33981 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(33981 / 31250) = 1/(31250 / 33981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3335 : Bounds (10472771 / 125000000) (83782169 / 1000000000) (Real.log (33981 / 31250)) := by
  have h := reflection_log_3335_neg
  have he : Real.log (33981 / 31250) = -Real.log (31250 / 33981) := by
    rw [show ((33981 / 31250) : ℝ) = ((31250 / 33981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3336_neg : (22862211 / 250000000) ≤ -Real.log (28519 / 31250) ∧
    -Real.log (28519 / 31250) ≤ (18289769 / 200000000) := by
  have h := checkLog_sound (w := (2731 / 59769)) (n := 12)
    (lo := (22862211 / 250000000)) (hi := (18289769 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 28519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 28519) = 1/(28519 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3336 : Bounds (-18289769 / 200000000) (-22862211 / 250000000) (Real.log (28519 / 31250)) := by
  have h := reflection_log_3336_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3337_neg : (10498633 / 125000000) ≤ -Real.log (1000000 / 1087617) ∧
    -Real.log (1000000 / 1087617) ≤ (16797813 / 200000000) := by
  have h := checkLog_sound (w := (87617 / 2087617)) (n := 12)
    (lo := (10498633 / 125000000)) (hi := (16797813 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1087617 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1087617 / 1000000) = 1/(1000000 / 1087617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3337 : Bounds (10498633 / 125000000) (16797813 / 200000000) (Real.log (1087617 / 1000000)) := by
  have h := reflection_log_3337_neg
  have he : Real.log (1087617 / 1000000) = -Real.log (1000000 / 1087617) := by
    rw [show ((1087617 / 1000000) : ℝ) = ((1000000 / 1087617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3338_neg : (4584771 / 50000000) ≤ -Real.log (912383 / 1000000) ∧
    -Real.log (912383 / 1000000) ≤ (91695421 / 1000000000) := by
  have h := checkLog_sound (w := (87617 / 1912383)) (n := 12)
    (lo := (4584771 / 50000000)) (hi := (91695421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 912383) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 912383) = 1/(912383 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3338 : Bounds (-91695421 / 1000000000) (-4584771 / 50000000) (Real.log (912383 / 1000000)) := by
  have h := reflection_log_3338_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3339_neg : (1926589 / 250000000) ≤ -Real.log (992323261311 / 1000000000000) ∧
    -Real.log (992323261311 / 1000000000000) ≤ (7706357 / 1000000000) := by
  have h := checkLog_sound (w := (7676738689 / 1992323261311)) (n := 12)
    (lo := (1926589 / 250000000)) (hi := (7706357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992323261311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992323261311) = 1/(992323261311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3339 : Bounds (-7706357 / 1000000000) (-1926589 / 250000000) (Real.log (992323261311 / 1000000000000)) := by
  have h := reflection_log_3339_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3340_neg : (306667 / 40000000) ≤ -Real.log (969104139 / 976562500) ∧
    -Real.log (969104139 / 976562500) ≤ (1916669 / 250000000) := by
  have h := checkLog_sound (w := (7458361 / 1945666639)) (n := 12)
    (lo := (306667 / 40000000)) (hi := (1916669 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 969104139) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 969104139) = 1/(969104139 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3340 : Bounds (-1916669 / 250000000) (-306667 / 40000000) (Real.log (969104139 / 976562500)) := by
  have h := reflection_log_3340_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3341_neg : (175231013 / 1000000000) ≤ -Real.log (250000000000 / 297880360461) ∧
    -Real.log (250000000000 / 297880360461) ≤ (87615507 / 500000000) := by
  have h := checkLog_sound (w := (47880360461 / 547880360461)) (n := 12)
    (lo := (175231013 / 1000000000)) (hi := (87615507 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297880360461 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297880360461 / 250000000000) = 1/(250000000000 / 297880360461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3341 : Bounds (175231013 / 1000000000) (87615507 / 500000000) (Real.log (297880360461 / 250000000000)) := by
  have h := reflection_log_3341_neg
  have he : Real.log (297880360461 / 250000000000) = -Real.log (250000000000 / 297880360461) := by
    rw [show ((297880360461 / 250000000000) : ℝ) = ((250000000000 / 297880360461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3342_neg : (35136897 / 200000000) ≤ -Real.log (250000000000 / 298015471573) ∧
    -Real.log (250000000000 / 298015471573) ≤ (87842243 / 500000000) := by
  have h := checkLog_sound (w := (48015471573 / 548015471573)) (n := 12)
    (lo := (35136897 / 200000000)) (hi := (87842243 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298015471573 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298015471573 / 250000000000) = 1/(250000000000 / 298015471573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3342 : Bounds (35136897 / 200000000) (87842243 / 500000000) (Real.log (298015471573 / 250000000000)) := by
  have h := reflection_log_3342_neg
  have he : Real.log (298015471573 / 250000000000) = -Real.log (250000000000 / 298015471573) := by
    rw [show ((298015471573 / 250000000000) : ℝ) = ((250000000000 / 298015471573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3343_neg : (175788613 / 500000000) ≤ -Real.log (250000000000 / 355326876513) ∧
    -Real.log (250000000000 / 355326876513) ≤ (351577227 / 1000000000) := by
  have h := checkLog_sound (w := (105326876513 / 605326876513)) (n := 12)
    (lo := (175788613 / 500000000)) (hi := (351577227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((355326876513 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(355326876513 / 250000000000) = 1/(250000000000 / 355326876513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3343 : Bounds (175788613 / 500000000) (351577227 / 1000000000) (Real.log (355326876513 / 250000000000)) := by
  have h := reflection_log_3343_neg
  have he : Real.log (355326876513 / 250000000000) = -Real.log (250000000000 / 355326876513) := by
    rw [show ((355326876513 / 250000000000) : ℝ) = ((250000000000 / 355326876513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3344_neg : (175891737 / 500000000) ≤ -Real.log (20000000000 / 28432013561) ∧
    -Real.log (20000000000 / 28432013561) ≤ (14071339 / 40000000) := by
  have h := checkLog_sound (w := (8432013561 / 48432013561)) (n := 12)
    (lo := (175891737 / 500000000)) (hi := (14071339 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28432013561 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(28432013561 / 20000000000) = 1/(20000000000 / 28432013561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3344 : Bounds (175891737 / 500000000) (14071339 / 40000000) (Real.log (28432013561 / 20000000000)) := by
  have h := reflection_log_3344_neg
  have he : Real.log (28432013561 / 20000000000) = -Real.log (20000000000 / 28432013561) := by
    rw [show ((28432013561 / 20000000000) : ℝ) = ((20000000000 / 28432013561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3345_neg : (20073383 / 125000000) ≤ -Real.log (5000 / 5871) ∧
    -Real.log (5000 / 5871) ≤ (32117413 / 200000000) := by
  have h := checkLog_sound (w := (871 / 10871)) (n := 12)
    (lo := (20073383 / 125000000)) (hi := (32117413 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5871 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5871 / 5000) = 1/(5000 / 5871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3345 : Bounds (20073383 / 125000000) (32117413 / 200000000) (Real.log (5871 / 5000)) := by
  have h := reflection_log_3345_neg
  have he : Real.log (5871 / 5000) = -Real.log (5000 / 5871) := by
    rw [show ((5871 / 5000) : ℝ) = ((5000 / 5871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3346_neg : (38280533 / 200000000) ≤ -Real.log (4129 / 5000) ∧
    -Real.log (4129 / 5000) ≤ (95701333 / 500000000) := by
  have h := checkLog_sound (w := (871 / 9129)) (n := 12)
    (lo := (38280533 / 200000000)) (hi := (95701333 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4129) = 1/(4129 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3346 : Bounds (-95701333 / 500000000) (-38280533 / 200000000) (Real.log (4129 / 5000)) := by
  have h := reflection_log_3346_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3347_neg : (21773 / 125000000) ≤ -Real.log (5000000 / 5000871) ∧
    -Real.log (5000000 / 5000871) ≤ (34837 / 200000000) := by
  have h := checkLog_sound (w := (871 / 10000871)) (n := 12)
    (lo := (21773 / 125000000)) (hi := (34837 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000871 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000871 / 5000000) = 1/(5000000 / 5000871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3347 : Bounds (21773 / 125000000) (34837 / 200000000) (Real.log (5000871 / 5000000)) := by
  have h := reflection_log_3347_neg
  have he : Real.log (5000871 / 5000000) = -Real.log (5000000 / 5000871) := by
    rw [show ((5000871 / 5000000) : ℝ) = ((5000000 / 5000871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3348_neg : (34843 / 200000000) ≤ -Real.log (4999129 / 5000000) ∧
    -Real.log (4999129 / 5000000) ≤ (21777 / 125000000) := by
  have h := checkLog_sound (w := (871 / 9999129)) (n := 12)
    (lo := (34843 / 200000000)) (hi := (21777 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999129) = 1/(4999129 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3348 : Bounds (-21777 / 125000000) (-34843 / 200000000) (Real.log (4999129 / 5000000)) := by
  have h := reflection_log_3348_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3349_neg : (20957267 / 250000000) ≤ -Real.log (1000000 / 1087443) ∧
    -Real.log (1000000 / 1087443) ≤ (83829069 / 1000000000) := by
  have h := checkLog_sound (w := (87443 / 2087443)) (n := 12)
    (lo := (20957267 / 250000000)) (hi := (83829069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1087443 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1087443 / 1000000) = 1/(1000000 / 1087443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3349 : Bounds (20957267 / 250000000) (83829069 / 1000000000) (Real.log (1087443 / 1000000)) := by
  have h := reflection_log_3349_neg
  have he : Real.log (1087443 / 1000000) = -Real.log (1000000 / 1087443) := by
    rw [show ((1087443 / 1000000) : ℝ) = ((1000000 / 1087443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3350_neg : (91504729 / 1000000000) ≤ -Real.log (912557 / 1000000) ∧
    -Real.log (912557 / 1000000) ≤ (9150473 / 100000000) := by
  have h := checkLog_sound (w := (87443 / 1912557)) (n := 12)
    (lo := (91504729 / 1000000000)) (hi := (9150473 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 912557) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 912557) = 1/(912557 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3350 : Bounds (-9150473 / 100000000) (-91504729 / 1000000000) (Real.log (912557 / 1000000)) := by
  have h := reflection_log_3350_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3351_neg : (42017977 / 500000000) ≤ -Real.log (250000 / 271917) ∧
    -Real.log (250000 / 271917) ≤ (16807191 / 200000000) := by
  have h := checkLog_sound (w := (21917 / 521917)) (n := 12)
    (lo := (42017977 / 500000000)) (hi := (16807191 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((271917 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(271917 / 250000) = 1/(250000 / 271917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3351 : Bounds (42017977 / 500000000) (16807191 / 200000000) (Real.log (271917 / 250000)) := by
  have h := reflection_log_3351_neg
  have he : Real.log (271917 / 250000) = -Real.log (250000 / 271917) := by
    rw [show ((271917 / 250000) : ℝ) = ((250000 / 271917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3352_neg : (2293783 / 25000000) ≤ -Real.log (228083 / 250000) ∧
    -Real.log (228083 / 250000) ≤ (91751321 / 1000000000) := by
  have h := checkLog_sound (w := (21917 / 478083)) (n := 12)
    (lo := (2293783 / 25000000)) (hi := (91751321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 228083) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 228083) = 1/(228083 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3352 : Bounds (-91751321 / 1000000000) (-2293783 / 25000000) (Real.log (228083 / 250000)) := by
  have h := reflection_log_3352_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3353_neg : (1543073 / 200000000) ≤ -Real.log (62019645111 / 62500000000) ∧
    -Real.log (62019645111 / 62500000000) ≤ (3857683 / 500000000) := by
  have h := checkLog_sound (w := (480354889 / 124519645111)) (n := 12)
    (lo := (1543073 / 200000000)) (hi := (3857683 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62019645111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62019645111) = 1/(62019645111 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3353 : Bounds (-3857683 / 500000000) (-1543073 / 200000000) (Real.log (62019645111 / 62500000000)) := by
  have h := reflection_log_3353_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3354_neg : (383783 / 50000000) ≤ -Real.log (992353721751 / 1000000000000) ∧
    -Real.log (992353721751 / 1000000000000) ≤ (7675661 / 1000000000) := by
  have h := checkLog_sound (w := (7646278249 / 1992353721751)) (n := 12)
    (lo := (383783 / 50000000)) (hi := (7675661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992353721751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992353721751) = 1/(992353721751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3354 : Bounds (-7675661 / 1000000000) (-383783 / 50000000) (Real.log (992353721751 / 1000000000000)) := by
  have h := reflection_log_3354_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3355_neg : (87666899 / 500000000) ≤ -Real.log (250000000000 / 297910979807) ∧
    -Real.log (250000000000 / 297910979807) ≤ (175333799 / 1000000000) := by
  have h := checkLog_sound (w := (47910979807 / 547910979807)) (n := 12)
    (lo := (87666899 / 500000000)) (hi := (175333799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297910979807 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297910979807 / 250000000000) = 1/(250000000000 / 297910979807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3355 : Bounds (87666899 / 500000000) (175333799 / 1000000000) (Real.log (297910979807 / 250000000000)) := by
  have h := reflection_log_3355_neg
  have he : Real.log (297910979807 / 250000000000) = -Real.log (250000000000 / 297910979807) := by
    rw [show ((297910979807 / 250000000000) : ℝ) = ((250000000000 / 297910979807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3356_neg : (87893637 / 500000000) ≤ -Real.log (250000000000 / 298046106023) ∧
    -Real.log (250000000000 / 298046106023) ≤ (7031491 / 40000000) := by
  have h := checkLog_sound (w := (48046106023 / 548046106023)) (n := 12)
    (lo := (87893637 / 500000000)) (hi := (7031491 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298046106023 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298046106023 / 250000000000) = 1/(250000000000 / 298046106023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3356 : Bounds (87893637 / 500000000) (7031491 / 40000000) (Real.log (298046106023 / 250000000000)) := by
  have h := reflection_log_3356_neg
  have he : Real.log (298046106023 / 250000000000) = -Real.log (250000000000 / 298046106023) := by
    rw [show ((298046106023 / 250000000000) : ℝ) = ((250000000000 / 298046106023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3357_neg : (175891737 / 500000000) ≤ -Real.log (31250000000 / 44425021189) ∧
    -Real.log (31250000000 / 44425021189) ≤ (14071339 / 40000000) := by
  have h := checkLog_sound (w := (13175021189 / 75675021189)) (n := 12)
    (lo := (175891737 / 500000000)) (hi := (14071339 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44425021189 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(44425021189 / 31250000000) = 1/(31250000000 / 44425021189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3357 : Bounds (175891737 / 500000000) (14071339 / 40000000) (Real.log (44425021189 / 31250000000)) := by
  have h := reflection_log_3357_neg
  have he : Real.log (44425021189 / 31250000000) = -Real.log (31250000000 / 44425021189) := by
    rw [show ((44425021189 / 31250000000) : ℝ) = ((31250000000 / 44425021189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3358_neg : (35198973 / 100000000) ≤ -Real.log (125000000000 / 177736740131) ∧
    -Real.log (125000000000 / 177736740131) ≤ (351989731 / 1000000000) := by
  have h := checkLog_sound (w := (52736740131 / 302736740131)) (n := 12)
    (lo := (35198973 / 100000000)) (hi := (351989731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((177736740131 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(177736740131 / 125000000000) = 1/(125000000000 / 177736740131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3358 : Bounds (35198973 / 100000000) (351989731 / 1000000000) (Real.log (177736740131 / 125000000000)) := by
  have h := reflection_log_3358_neg
  have he : Real.log (177736740131 / 125000000000) = -Real.log (125000000000 / 177736740131) := by
    rw [show ((177736740131 / 125000000000) : ℝ) = ((125000000000 / 177736740131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3359_neg : (6426889 / 40000000) ≤ -Real.log (10000 / 11743) ∧
    -Real.log (10000 / 11743) ≤ (80336113 / 500000000) := by
  have h := checkLog_sound (w := (1743 / 21743)) (n := 12)
    (lo := (6426889 / 40000000)) (hi := (80336113 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11743 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11743 / 10000) = 1/(10000 / 11743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3359 : Bounds (6426889 / 40000000) (80336113 / 500000000) (Real.log (11743 / 10000)) := by
  have h := reflection_log_3359_neg
  have he : Real.log (11743 / 10000) = -Real.log (10000 / 11743) := by
    rw [show ((11743 / 10000) : ℝ) = ((10000 / 11743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3360_neg : (191523767 / 1000000000) ≤ -Real.log (8257 / 10000) ∧
    -Real.log (8257 / 10000) ≤ (23940471 / 125000000) := by
  have h := checkLog_sound (w := (1743 / 18257)) (n := 12)
    (lo := (191523767 / 1000000000)) (hi := (23940471 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8257) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8257) = 1/(8257 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3360 : Bounds (-23940471 / 125000000) (-191523767 / 1000000000) (Real.log (8257 / 10000)) := by
  have h := reflection_log_3360_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3361_neg : (43571 / 250000000) ≤ -Real.log (10000000 / 10001743) ∧
    -Real.log (10000000 / 10001743) ≤ (34857 / 200000000) := by
  have h := checkLog_sound (w := (1743 / 20001743)) (n := 12)
    (lo := (43571 / 250000000)) (hi := (34857 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001743 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001743 / 10000000) = 1/(10000000 / 10001743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3361 : Bounds (43571 / 250000000) (34857 / 200000000) (Real.log (10001743 / 10000000)) := by
  have h := reflection_log_3361_neg
  have he : Real.log (10001743 / 10000000) = -Real.log (10000000 / 10001743) := by
    rw [show ((10001743 / 10000000) : ℝ) = ((10000000 / 10001743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3362_neg : (34863 / 200000000) ≤ -Real.log (9998257 / 10000000) ∧
    -Real.log (9998257 / 10000000) ≤ (43579 / 250000000) := by
  have h := checkLog_sound (w := (1743 / 19998257)) (n := 12)
    (lo := (34863 / 200000000)) (hi := (43579 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998257) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998257) = 1/(9998257 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3362 : Bounds (-43579 / 250000000) (-34863 / 200000000) (Real.log (9998257 / 10000000)) := by
  have h := reflection_log_3362_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3363_neg : (41937983 / 500000000) ≤ -Real.log (500000 / 543747) ∧
    -Real.log (500000 / 543747) ≤ (83875967 / 1000000000) := by
  have h := checkLog_sound (w := (43747 / 1043747)) (n := 12)
    (lo := (41937983 / 500000000)) (hi := (83875967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((543747 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(543747 / 500000) = 1/(500000 / 543747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3363 : Bounds (41937983 / 500000000) (83875967 / 1000000000) (Real.log (543747 / 500000)) := by
  have h := reflection_log_3363_neg
  have he : Real.log (543747 / 500000) = -Real.log (500000 / 543747) := by
    rw [show ((543747 / 500000) : ℝ) = ((500000 / 543747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3364_neg : (45780309 / 500000000) ≤ -Real.log (456253 / 500000) ∧
    -Real.log (456253 / 500000) ≤ (91560619 / 1000000000) := by
  have h := checkLog_sound (w := (43747 / 956253)) (n := 12)
    (lo := (45780309 / 500000000)) (hi := (91560619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 456253) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 456253) = 1/(456253 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3364 : Bounds (-91560619 / 1000000000) (-45780309 / 500000000) (Real.log (456253 / 500000)) := by
  have h := reflection_log_3364_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3365_neg : (84082843 / 1000000000) ≤ -Real.log (1000000 / 1087719) ∧
    -Real.log (1000000 / 1087719) ≤ (21020711 / 250000000) := by
  have h := checkLog_sound (w := (87719 / 2087719)) (n := 12)
    (lo := (84082843 / 1000000000)) (hi := (21020711 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1087719 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1087719 / 1000000) = 1/(1000000 / 1087719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3365 : Bounds (84082843 / 1000000000) (21020711 / 250000000) (Real.log (1087719 / 1000000)) := by
  have h := reflection_log_3365_neg
  have he : Real.log (1087719 / 1000000) = -Real.log (1000000 / 1087719) := by
    rw [show ((1087719 / 1000000) : ℝ) = ((1000000 / 1087719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3366_neg : (45903611 / 500000000) ≤ -Real.log (912281 / 1000000) ∧
    -Real.log (912281 / 1000000) ≤ (91807223 / 1000000000) := by
  have h := checkLog_sound (w := (87719 / 1912281)) (n := 12)
    (lo := (45903611 / 500000000)) (hi := (91807223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 912281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 912281) = 1/(912281 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3366 : Bounds (-91807223 / 1000000000) (-45903611 / 500000000) (Real.log (912281 / 1000000)) := by
  have h := reflection_log_3366_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3367_neg : (7724379 / 1000000000) ≤ -Real.log (992305377039 / 1000000000000) ∧
    -Real.log (992305377039 / 1000000000000) ≤ (386219 / 50000000) := by
  have h := checkLog_sound (w := (7694622961 / 1992305377039)) (n := 12)
    (lo := (7724379 / 1000000000)) (hi := (386219 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992305377039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992305377039) = 1/(992305377039 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3367 : Bounds (-386219 / 50000000) (-7724379 / 1000000000) (Real.log (992305377039 / 1000000000000)) := by
  have h := reflection_log_3367_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3368_neg : (7684651 / 1000000000) ≤ -Real.log (248086199991 / 250000000000) ∧
    -Real.log (248086199991 / 250000000000) ≤ (1921163 / 250000000) := by
  have h := checkLog_sound (w := (1913800009 / 498086199991)) (n := 12)
    (lo := (7684651 / 1000000000)) (hi := (1921163 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248086199991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248086199991) = 1/(248086199991 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3368 : Bounds (-1921163 / 250000000) (-7684651 / 1000000000) (Real.log (248086199991 / 250000000000)) := by
  have h := reflection_log_3368_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3369_neg : (21929573 / 125000000) ≤ -Real.log (500000000000 / 595883205151) ∧
    -Real.log (500000000000 / 595883205151) ≤ (35087317 / 200000000) := by
  have h := checkLog_sound (w := (95883205151 / 1095883205151)) (n := 12)
    (lo := (21929573 / 125000000)) (hi := (35087317 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((595883205151 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(595883205151 / 500000000000) = 1/(500000000000 / 595883205151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3369 : Bounds (21929573 / 125000000) (35087317 / 200000000) (Real.log (595883205151 / 500000000000)) := by
  have h := reflection_log_3369_neg
  have he : Real.log (595883205151 / 500000000000) = -Real.log (500000000000 / 595883205151) := by
    rw [show ((595883205151 / 500000000000) : ℝ) = ((500000000000 / 595883205151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3370_neg : (35178013 / 200000000) ≤ -Real.log (125000000000 / 149038371949) ∧
    -Real.log (125000000000 / 149038371949) ≤ (87945033 / 500000000) := by
  have h := checkLog_sound (w := (24038371949 / 274038371949)) (n := 12)
    (lo := (35178013 / 200000000)) (hi := (87945033 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149038371949 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149038371949 / 125000000000) = 1/(125000000000 / 149038371949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3370 : Bounds (35178013 / 200000000) (87945033 / 500000000) (Real.log (149038371949 / 125000000000)) := by
  have h := reflection_log_3370_neg
  have he : Real.log (149038371949 / 125000000000) = -Real.log (125000000000 / 149038371949) := by
    rw [show ((149038371949 / 125000000000) : ℝ) = ((125000000000 / 149038371949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3371_neg : (35198973 / 100000000) ≤ -Real.log (500000000000 / 710946960523) ∧
    -Real.log (500000000000 / 710946960523) ≤ (351989731 / 1000000000) := by
  have h := checkLog_sound (w := (210946960523 / 1210946960523)) (n := 12)
    (lo := (35198973 / 100000000)) (hi := (351989731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((710946960523 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(710946960523 / 500000000000) = 1/(500000000000 / 710946960523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3371 : Bounds (35198973 / 100000000) (351989731 / 1000000000) (Real.log (710946960523 / 500000000000)) := by
  have h := reflection_log_3371_neg
  have he : Real.log (710946960523 / 500000000000) = -Real.log (500000000000 / 710946960523) := by
    rw [show ((710946960523 / 500000000000) : ℝ) = ((500000000000 / 710946960523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3372_neg : (44024499 / 125000000) ≤ -Real.log (500000000000 / 711093617537) ∧
    -Real.log (500000000000 / 711093617537) ≤ (352195993 / 1000000000) := by
  have h := checkLog_sound (w := (211093617537 / 1211093617537)) (n := 12)
    (lo := (44024499 / 125000000)) (hi := (352195993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((711093617537 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(711093617537 / 500000000000) = 1/(500000000000 / 711093617537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3372 : Bounds (44024499 / 125000000) (352195993 / 1000000000) (Real.log (711093617537 / 500000000000)) := by
  have h := reflection_log_3372_neg
  have he : Real.log (711093617537 / 500000000000) = -Real.log (500000000000 / 711093617537) := by
    rw [show ((711093617537 / 500000000000) : ℝ) = ((500000000000 / 711093617537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3373_neg : (80378689 / 500000000) ≤ -Real.log (625 / 734) ∧
    -Real.log (625 / 734) ≤ (160757379 / 1000000000) := by
  have h := checkLog_sound (w := (109 / 1359)) (n := 12)
    (lo := (80378689 / 500000000)) (hi := (160757379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((734 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(734 / 625) = 1/(625 / 734) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3373 : Bounds (80378689 / 500000000) (160757379 / 1000000000) (Real.log (734 / 625)) := by
  have h := reflection_log_3373_neg
  have he : Real.log (734 / 625) = -Real.log (625 / 734) := by
    rw [show ((734 / 625) : ℝ) = ((625 / 734) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3374_neg : (47911221 / 250000000) ≤ -Real.log (516 / 625) ∧
    -Real.log (516 / 625) ≤ (38328977 / 200000000) := by
  have h := checkLog_sound (w := (109 / 1141)) (n := 12)
    (lo := (47911221 / 250000000)) (hi := (38328977 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 516) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 516) = 1/(516 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3374 : Bounds (-38328977 / 200000000) (-47911221 / 250000000) (Real.log (516 / 625)) := by
  have h := reflection_log_3374_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3375_neg : (10899 / 62500000) ≤ -Real.log (625000 / 625109) ∧
    -Real.log (625000 / 625109) ≤ (34877 / 200000000) := by
  have h := checkLog_sound (w := (109 / 1250109)) (n := 12)
    (lo := (10899 / 62500000)) (hi := (34877 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625109 / 625000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625109 / 625000) = 1/(625000 / 625109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3375 : Bounds (10899 / 62500000) (34877 / 200000000) (Real.log (625109 / 625000)) := by
  have h := reflection_log_3375_neg
  have he : Real.log (625109 / 625000) = -Real.log (625000 / 625109) := by
    rw [show ((625109 / 625000) : ℝ) = ((625000 / 625109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3376_neg : (34883 / 200000000) ≤ -Real.log (624891 / 625000) ∧
    -Real.log (624891 / 625000) ≤ (10901 / 62500000) := by
  have h := checkLog_sound (w := (109 / 1249891)) (n := 12)
    (lo := (34883 / 200000000)) (hi := (10901 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000 / 624891) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000 / 624891) = 1/(624891 / 625000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3376 : Bounds (-10901 / 62500000) (-34883 / 200000000) (Real.log (624891 / 625000)) := by
  have h := reflection_log_3376_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3377_neg : (41961431 / 500000000) ≤ -Real.log (200000 / 217509) ∧
    -Real.log (200000 / 217509) ≤ (83922863 / 1000000000) := by
  have h := checkLog_sound (w := (17509 / 417509)) (n := 12)
    (lo := (41961431 / 500000000)) (hi := (83922863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((217509 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(217509 / 200000) = 1/(200000 / 217509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3377 : Bounds (41961431 / 500000000) (83922863 / 1000000000) (Real.log (217509 / 200000)) := by
  have h := reflection_log_3377_neg
  have he : Real.log (217509 / 200000) = -Real.log (200000 / 217509) := by
    rw [show ((217509 / 200000) : ℝ) = ((200000 / 217509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3378_neg : (91616509 / 1000000000) ≤ -Real.log (182491 / 200000) ∧
    -Real.log (182491 / 200000) ≤ (9161651 / 100000000) := by
  have h := checkLog_sound (w := (17509 / 382491)) (n := 12)
    (lo := (91616509 / 1000000000)) (hi := (9161651 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 182491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 182491) = 1/(182491 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3378 : Bounds (-9161651 / 100000000) (-91616509 / 1000000000) (Real.log (182491 / 200000)) := by
  have h := reflection_log_3378_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3379_neg : (84129729 / 1000000000) ≤ -Real.log (100000 / 108777) ∧
    -Real.log (100000 / 108777) ≤ (8412973 / 100000000) := by
  have h := checkLog_sound (w := (8777 / 208777)) (n := 12)
    (lo := (84129729 / 1000000000)) (hi := (8412973 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((108777 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(108777 / 100000) = 1/(100000 / 108777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3379 : Bounds (84129729 / 1000000000) (8412973 / 100000000) (Real.log (108777 / 100000)) := by
  have h := reflection_log_3379_neg
  have he : Real.log (108777 / 100000) = -Real.log (100000 / 108777) := by
    rw [show ((108777 / 100000) : ℝ) = ((100000 / 108777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3380_neg : (91863127 / 1000000000) ≤ -Real.log (91223 / 100000) ∧
    -Real.log (91223 / 100000) ≤ (11482891 / 125000000) := by
  have h := checkLog_sound (w := (8777 / 191223)) (n := 12)
    (lo := (91863127 / 1000000000)) (hi := (11482891 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 91223) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 91223) = 1/(91223 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3380 : Bounds (-11482891 / 125000000) (-91863127 / 1000000000) (Real.log (91223 / 100000)) := by
  have h := reflection_log_3380_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3381_neg : (3866699 / 500000000) ≤ -Real.log (9922964271 / 10000000000) ∧
    -Real.log (9922964271 / 10000000000) ≤ (7733399 / 1000000000) := by
  have h := checkLog_sound (w := (77035729 / 19922964271)) (n := 12)
    (lo := (3866699 / 500000000)) (hi := (7733399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9922964271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9922964271) = 1/(9922964271 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3381 : Bounds (-7733399 / 1000000000) (-3866699 / 500000000) (Real.log (9922964271 / 10000000000)) := by
  have h := reflection_log_3381_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3382_neg : (7693647 / 1000000000) ≤ -Real.log (39693434919 / 40000000000) ∧
    -Real.log (39693434919 / 40000000000) ≤ (480853 / 62500000) := by
  have h := checkLog_sound (w := (306565081 / 79693434919)) (n := 12)
    (lo := (7693647 / 1000000000)) (hi := (480853 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39693434919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39693434919) = 1/(39693434919 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3382 : Bounds (-480853 / 62500000) (-7693647 / 1000000000) (Real.log (39693434919 / 40000000000)) := by
  have h := reflection_log_3382_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3383_neg : (43884843 / 250000000) ≤ -Real.log (250000000000 / 297972228767) ∧
    -Real.log (250000000000 / 297972228767) ≤ (175539373 / 1000000000) := by
  have h := checkLog_sound (w := (47972228767 / 547972228767)) (n := 12)
    (lo := (43884843 / 250000000)) (hi := (175539373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297972228767 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297972228767 / 250000000000) = 1/(250000000000 / 297972228767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3383 : Bounds (43884843 / 250000000) (175539373 / 1000000000) (Real.log (297972228767 / 250000000000)) := by
  have h := reflection_log_3383_neg
  have he : Real.log (297972228767 / 250000000000) = -Real.log (250000000000 / 297972228767) := by
    rw [show ((297972228767 / 250000000000) : ℝ) = ((250000000000 / 297972228767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3384_neg : (21999107 / 125000000) ≤ -Real.log (250000000000 / 298107385199) ∧
    -Real.log (250000000000 / 298107385199) ≤ (175992857 / 1000000000) := by
  have h := checkLog_sound (w := (48107385199 / 548107385199)) (n := 12)
    (lo := (21999107 / 125000000)) (hi := (175992857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298107385199 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298107385199 / 250000000000) = 1/(250000000000 / 298107385199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3384 : Bounds (21999107 / 125000000) (175992857 / 1000000000) (Real.log (298107385199 / 250000000000)) := by
  have h := reflection_log_3384_neg
  have he : Real.log (298107385199 / 250000000000) = -Real.log (250000000000 / 298107385199) := by
    rw [show ((298107385199 / 250000000000) : ℝ) = ((250000000000 / 298107385199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3385_neg : (44024499 / 125000000) ≤ -Real.log (3906250000 / 5555418887) ∧
    -Real.log (3906250000 / 5555418887) ≤ (352195993 / 1000000000) := by
  have h := checkLog_sound (w := (1649168887 / 9461668887)) (n := 12)
    (lo := (44024499 / 125000000)) (hi := (352195993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5555418887 / 3906250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5555418887 / 3906250000) = 1/(3906250000 / 5555418887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3385 : Bounds (44024499 / 125000000) (352195993 / 1000000000) (Real.log (5555418887 / 3906250000)) := by
  have h := reflection_log_3385_neg
  have he : Real.log (5555418887 / 3906250000) = -Real.log (3906250000 / 5555418887) := by
    rw [show ((5555418887 / 3906250000) : ℝ) = ((3906250000 / 5555418887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3386_neg : (352402263 / 1000000000) ≤ -Real.log (250000000000 / 355620155039) ∧
    -Real.log (250000000000 / 355620155039) ≤ (44050283 / 125000000) := by
  have h := checkLog_sound (w := (105620155039 / 605620155039)) (n := 12)
    (lo := (352402263 / 1000000000)) (hi := (44050283 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((355620155039 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(355620155039 / 250000000000) = 1/(250000000000 / 355620155039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3386 : Bounds (352402263 / 1000000000) (44050283 / 125000000) (Real.log (355620155039 / 250000000000)) := by
  have h := reflection_log_3386_neg
  have he : Real.log (355620155039 / 250000000000) = -Real.log (250000000000 / 355620155039) := by
    rw [show ((355620155039 / 250000000000) : ℝ) = ((250000000000 / 355620155039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3387_neg : (6433701 / 40000000) ≤ -Real.log (2000 / 2349) ∧
    -Real.log (2000 / 2349) ≤ (80421263 / 500000000) := by
  have h := checkLog_sound (w := (349 / 4349)) (n := 12)
    (lo := (6433701 / 40000000)) (hi := (80421263 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2349 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2349 / 2000) = 1/(2000 / 2349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3387 : Bounds (6433701 / 40000000) (80421263 / 500000000) (Real.log (2349 / 2000)) := by
  have h := reflection_log_3387_neg
  have he : Real.log (2349 / 2000) = -Real.log (2000 / 2349) := by
    rw [show ((2349 / 2000) : ℝ) = ((2000 / 2349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3388_neg : (38353203 / 200000000) ≤ -Real.log (1651 / 2000) ∧
    -Real.log (1651 / 2000) ≤ (374543 / 1953125) := by
  have h := checkLog_sound (w := (349 / 3651)) (n := 12)
    (lo := (38353203 / 200000000)) (hi := (374543 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1651) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1651) = 1/(1651 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3388 : Bounds (-374543 / 1953125) (-38353203 / 200000000) (Real.log (1651 / 2000)) := by
  have h := reflection_log_3388_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3389_neg : (43621 / 250000000) ≤ -Real.log (2000000 / 2000349) ∧
    -Real.log (2000000 / 2000349) ≤ (34897 / 200000000) := by
  have h := checkLog_sound (w := (349 / 4000349)) (n := 12)
    (lo := (43621 / 250000000)) (hi := (34897 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000349 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000349 / 2000000) = 1/(2000000 / 2000349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3389 : Bounds (43621 / 250000000) (34897 / 200000000) (Real.log (2000349 / 2000000)) := by
  have h := reflection_log_3389_neg
  have he : Real.log (2000349 / 2000000) = -Real.log (2000000 / 2000349) := by
    rw [show ((2000349 / 2000000) : ℝ) = ((2000000 / 2000349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3390_neg : (34903 / 200000000) ≤ -Real.log (1999651 / 2000000) ∧
    -Real.log (1999651 / 2000000) ≤ (43629 / 250000000) := by
  have h := checkLog_sound (w := (349 / 3999651)) (n := 12)
    (lo := (34903 / 200000000)) (hi := (43629 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999651) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999651) = 1/(1999651 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3390 : Bounds (-43629 / 250000000) (-34903 / 200000000) (Real.log (1999651 / 2000000)) := by
  have h := reflection_log_3390_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3391_neg : (20992209 / 250000000) ≤ -Real.log (200000 / 217519) ∧
    -Real.log (200000 / 217519) ≤ (83968837 / 1000000000) := by
  have h := checkLog_sound (w := (17519 / 417519)) (n := 12)
    (lo := (20992209 / 250000000)) (hi := (83968837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((217519 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(217519 / 200000) = 1/(200000 / 217519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3391 : Bounds (20992209 / 250000000) (83968837 / 1000000000) (Real.log (217519 / 200000)) := by
  have h := reflection_log_3391_neg
  have he : Real.log (217519 / 200000) = -Real.log (200000 / 217519) := by
    rw [show ((217519 / 200000) : ℝ) = ((200000 / 217519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0053 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_3392_neg : (22917827 / 250000000) ≤ -Real.log (182481 / 200000) ∧
    -Real.log (182481 / 200000) ≤ (91671309 / 1000000000) := by
  have h := checkLog_sound (w := (17519 / 382481)) (n := 12)
    (lo := (22917827 / 250000000)) (hi := (91671309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 182481) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 182481) = 1/(182481 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3392 : Bounds (-91671309 / 1000000000) (-22917827 / 250000000) (Real.log (182481 / 200000)) := by
  have h := reflection_log_3392_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3393_neg : (21044153 / 250000000) ≤ -Real.log (1000000 / 1087821) ∧
    -Real.log (1000000 / 1087821) ≤ (84176613 / 1000000000) := by
  have h := checkLog_sound (w := (87821 / 2087821)) (n := 12)
    (lo := (21044153 / 250000000)) (hi := (84176613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1087821 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1087821 / 1000000) = 1/(1000000 / 1087821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3393 : Bounds (21044153 / 250000000) (84176613 / 1000000000) (Real.log (1087821 / 1000000)) := by
  have h := reflection_log_3393_neg
  have he : Real.log (1087821 / 1000000) = -Real.log (1000000 / 1087821) := by
    rw [show ((1087821 / 1000000) : ℝ) = ((1000000 / 1087821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3394_neg : (22979759 / 250000000) ≤ -Real.log (912179 / 1000000) ∧
    -Real.log (912179 / 1000000) ≤ (91919037 / 1000000000) := by
  have h := checkLog_sound (w := (87821 / 1912179)) (n := 12)
    (lo := (22979759 / 250000000)) (hi := (91919037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 912179) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 912179) = 1/(912179 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3394 : Bounds (-91919037 / 1000000000) (-22979759 / 250000000) (Real.log (912179 / 1000000)) := by
  have h := reflection_log_3394_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3395_neg : (7742423 / 1000000000) ≤ -Real.log (992287471959 / 1000000000000) ∧
    -Real.log (992287471959 / 1000000000000) ≤ (967803 / 125000000) := by
  have h := checkLog_sound (w := (7712528041 / 1992287471959)) (n := 12)
    (lo := (7742423 / 1000000000)) (hi := (967803 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992287471959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992287471959) = 1/(992287471959 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3395 : Bounds (-967803 / 125000000) (-7742423 / 1000000000) (Real.log (992287471959 / 1000000000000)) := by
  have h := reflection_log_3395_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3396_neg : (962809 / 125000000) ≤ -Real.log (39693084639 / 40000000000) ∧
    -Real.log (39693084639 / 40000000000) ≤ (7702473 / 1000000000) := by
  have h := checkLog_sound (w := (306915361 / 79693084639)) (n := 12)
    (lo := (962809 / 125000000)) (hi := (7702473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39693084639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39693084639) = 1/(39693084639 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3396 : Bounds (-7702473 / 1000000000) (-962809 / 125000000) (Real.log (39693084639 / 40000000000)) := by
  have h := reflection_log_3396_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3397_neg : (35128029 / 200000000) ≤ -Real.log (250000000000 / 298002257769) ∧
    -Real.log (250000000000 / 298002257769) ≤ (87820073 / 500000000) := by
  have h := checkLog_sound (w := (48002257769 / 548002257769)) (n := 12)
    (lo := (35128029 / 200000000)) (hi := (87820073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298002257769 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298002257769 / 250000000000) = 1/(250000000000 / 298002257769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3397 : Bounds (35128029 / 200000000) (87820073 / 500000000) (Real.log (298002257769 / 250000000000)) := by
  have h := reflection_log_3397_neg
  have he : Real.log (298002257769 / 250000000000) = -Real.log (250000000000 / 298002257769) := by
    rw [show ((298002257769 / 250000000000) : ℝ) = ((250000000000 / 298002257769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3398_neg : (176095649 / 1000000000) ≤ -Real.log (500000000000 / 596276059853) ∧
    -Real.log (500000000000 / 596276059853) ≤ (3521913 / 20000000) := by
  have h := checkLog_sound (w := (96276059853 / 1096276059853)) (n := 12)
    (lo := (176095649 / 1000000000)) (hi := (3521913 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((596276059853 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(596276059853 / 500000000000) = 1/(500000000000 / 596276059853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3398 : Bounds (176095649 / 1000000000) (3521913 / 20000000) (Real.log (596276059853 / 500000000000)) := by
  have h := reflection_log_3398_neg
  have he : Real.log (596276059853 / 500000000000) = -Real.log (500000000000 / 596276059853) := by
    rw [show ((596276059853 / 500000000000) : ℝ) = ((500000000000 / 596276059853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3399_neg : (352402263 / 1000000000) ≤ -Real.log (500000000000 / 711240310077) ∧
    -Real.log (500000000000 / 711240310077) ≤ (44050283 / 125000000) := by
  have h := checkLog_sound (w := (211240310077 / 1211240310077)) (n := 12)
    (lo := (352402263 / 1000000000)) (hi := (44050283 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((711240310077 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(711240310077 / 500000000000) = 1/(500000000000 / 711240310077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3399 : Bounds (352402263 / 1000000000) (44050283 / 125000000) (Real.log (711240310077 / 500000000000)) := by
  have h := reflection_log_3399_neg
  have he : Real.log (711240310077 / 500000000000) = -Real.log (500000000000 / 711240310077) := by
    rw [show ((711240310077 / 500000000000) : ℝ) = ((500000000000 / 711240310077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3400_neg : (17630427 / 50000000) ≤ -Real.log (500000000000 / 711387038159) ∧
    -Real.log (500000000000 / 711387038159) ≤ (352608541 / 1000000000) := by
  have h := checkLog_sound (w := (211387038159 / 1211387038159)) (n := 12)
    (lo := (17630427 / 50000000)) (hi := (352608541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((711387038159 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(711387038159 / 500000000000) = 1/(500000000000 / 711387038159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3400 : Bounds (17630427 / 50000000) (352608541 / 1000000000) (Real.log (711387038159 / 500000000000)) := by
  have h := reflection_log_3400_neg
  have he : Real.log (711387038159 / 500000000000) = -Real.log (500000000000 / 711387038159) := by
    rw [show ((711387038159 / 500000000000) : ℝ) = ((500000000000 / 711387038159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3401_neg : (10057979 / 62500000) ≤ -Real.log (5000 / 5873) ∧
    -Real.log (5000 / 5873) ≤ (32185533 / 200000000) := by
  have h := checkLog_sound (w := (873 / 10873)) (n := 12)
    (lo := (10057979 / 62500000)) (hi := (32185533 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5873 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5873 / 5000) = 1/(5000 / 5873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3401 : Bounds (10057979 / 62500000) (32185533 / 200000000) (Real.log (5873 / 5000)) := by
  have h := reflection_log_3401_neg
  have he : Real.log (5873 / 5000) = -Real.log (5000 / 5873) := by
    rw [show ((5873 / 5000) : ℝ) = ((5000 / 5873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3402_neg : (191887161 / 1000000000) ≤ -Real.log (4127 / 5000) ∧
    -Real.log (4127 / 5000) ≤ (95943581 / 500000000) := by
  have h := checkLog_sound (w := (873 / 9127)) (n := 12)
    (lo := (191887161 / 1000000000)) (hi := (95943581 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4127) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4127) = 1/(4127 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3402 : Bounds (-95943581 / 500000000) (-191887161 / 1000000000) (Real.log (4127 / 5000)) := by
  have h := reflection_log_3402_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3403_neg : (21823 / 125000000) ≤ -Real.log (5000000 / 5000873) ∧
    -Real.log (5000000 / 5000873) ≤ (34917 / 200000000) := by
  have h := checkLog_sound (w := (873 / 10000873)) (n := 12)
    (lo := (21823 / 125000000)) (hi := (34917 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000873 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000873 / 5000000) = 1/(5000000 / 5000873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3403 : Bounds (21823 / 125000000) (34917 / 200000000) (Real.log (5000873 / 5000000)) := by
  have h := reflection_log_3403_neg
  have he : Real.log (5000873 / 5000000) = -Real.log (5000000 / 5000873) := by
    rw [show ((5000873 / 5000000) : ℝ) = ((5000000 / 5000873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3404_neg : (34923 / 200000000) ≤ -Real.log (4999127 / 5000000) ∧
    -Real.log (4999127 / 5000000) ≤ (21827 / 125000000) := by
  have h := checkLog_sound (w := (873 / 9999127)) (n := 12)
    (lo := (34923 / 200000000)) (hi := (21827 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999127) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999127) = 1/(4999127 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3404 : Bounds (-21827 / 125000000) (-34923 / 200000000) (Real.log (4999127 / 5000000)) := by
  have h := reflection_log_3404_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3405_neg : (84015727 / 1000000000) ≤ -Real.log (500000 / 543823) ∧
    -Real.log (500000 / 543823) ≤ (5250983 / 62500000) := by
  have h := checkLog_sound (w := (43823 / 1043823)) (n := 12)
    (lo := (84015727 / 1000000000)) (hi := (5250983 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((543823 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(543823 / 500000) = 1/(500000 / 543823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3405 : Bounds (84015727 / 1000000000) (5250983 / 62500000) (Real.log (543823 / 500000)) := by
  have h := reflection_log_3405_neg
  have he : Real.log (543823 / 500000) = -Real.log (500000 / 543823) := by
    rw [show ((543823 / 500000) : ℝ) = ((500000 / 543823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3406_neg : (45863603 / 500000000) ≤ -Real.log (456177 / 500000) ∧
    -Real.log (456177 / 500000) ≤ (91727207 / 1000000000) := by
  have h := checkLog_sound (w := (43823 / 956177)) (n := 12)
    (lo := (45863603 / 500000000)) (hi := (91727207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 456177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 456177) = 1/(456177 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3406 : Bounds (-91727207 / 1000000000) (-45863603 / 500000000) (Real.log (456177 / 500000)) := by
  have h := reflection_log_3406_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3407_neg : (42111747 / 500000000) ≤ -Real.log (15625 / 16998) ∧
    -Real.log (15625 / 16998) ≤ (16844699 / 200000000) := by
  have h := checkLog_sound (w := (1373 / 32623)) (n := 12)
    (lo := (42111747 / 500000000)) (hi := (16844699 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16998 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16998 / 15625) = 1/(15625 / 16998) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3407 : Bounds (42111747 / 500000000) (16844699 / 200000000) (Real.log (16998 / 15625)) := by
  have h := reflection_log_3407_neg
  have he : Real.log (16998 / 15625) = -Real.log (15625 / 16998) := by
    rw [show ((16998 / 15625) : ℝ) = ((15625 / 16998) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3408_neg : (91974947 / 1000000000) ≤ -Real.log (14252 / 15625) ∧
    -Real.log (14252 / 15625) ≤ (22993737 / 250000000) := by
  have h := checkLog_sound (w := (1373 / 29877)) (n := 12)
    (lo := (91974947 / 1000000000)) (hi := (22993737 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14252) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 14252) = 1/(14252 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3408 : Bounds (-22993737 / 250000000) (-91974947 / 1000000000) (Real.log (14252 / 15625)) := by
  have h := reflection_log_3408_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3409_neg : (7751453 / 1000000000) ≤ -Real.log (242255496 / 244140625) ∧
    -Real.log (242255496 / 244140625) ≤ (3875727 / 500000000) := by
  have h := checkLog_sound (w := (1885129 / 486396121)) (n := 12)
    (lo := (7751453 / 1000000000)) (hi := (3875727 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 242255496) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 242255496) = 1/(242255496 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3409 : Bounds (-3875727 / 500000000) (-7751453 / 1000000000) (Real.log (242255496 / 244140625)) := by
  have h := reflection_log_3409_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3410_neg : (3855739 / 500000000) ≤ -Real.log (248079544671 / 250000000000) ∧
    -Real.log (248079544671 / 250000000000) ≤ (7711479 / 1000000000) := by
  have h := checkLog_sound (w := (1920455329 / 498079544671)) (n := 12)
    (lo := (3855739 / 500000000)) (hi := (7711479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248079544671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248079544671) = 1/(248079544671 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3410 : Bounds (-7711479 / 1000000000) (-3855739 / 500000000) (Real.log (248079544671 / 250000000000)) := by
  have h := reflection_log_3410_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3411_neg : (87871467 / 500000000) ≤ -Real.log (500000000000 / 596065781483) ∧
    -Real.log (500000000000 / 596065781483) ≤ (35148587 / 200000000) := by
  have h := checkLog_sound (w := (96065781483 / 1096065781483)) (n := 12)
    (lo := (87871467 / 500000000)) (hi := (35148587 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((596065781483 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(596065781483 / 500000000000) = 1/(500000000000 / 596065781483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3411 : Bounds (87871467 / 500000000) (35148587 / 200000000) (Real.log (596065781483 / 500000000000)) := by
  have h := reflection_log_3411_neg
  have he : Real.log (596065781483 / 500000000000) = -Real.log (500000000000 / 596065781483) := by
    rw [show ((596065781483 / 500000000000) : ℝ) = ((500000000000 / 596065781483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3412_neg : (88099221 / 500000000) ≤ -Real.log (500000000000 / 596337356161) ∧
    -Real.log (500000000000 / 596337356161) ≤ (176198443 / 1000000000) := by
  have h := checkLog_sound (w := (96337356161 / 1096337356161)) (n := 12)
    (lo := (88099221 / 500000000)) (hi := (176198443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((596337356161 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(596337356161 / 500000000000) = 1/(500000000000 / 596337356161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3412 : Bounds (88099221 / 500000000) (176198443 / 1000000000) (Real.log (596337356161 / 500000000000)) := by
  have h := reflection_log_3412_neg
  have he : Real.log (596337356161 / 500000000000) = -Real.log (500000000000 / 596337356161) := by
    rw [show ((596337356161 / 500000000000) : ℝ) = ((500000000000 / 596337356161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3413_neg : (17630427 / 50000000) ≤ -Real.log (250000000000 / 355693519079) ∧
    -Real.log (250000000000 / 355693519079) ≤ (352608541 / 1000000000) := by
  have h := checkLog_sound (w := (105693519079 / 605693519079)) (n := 12)
    (lo := (17630427 / 50000000)) (hi := (352608541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((355693519079 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(355693519079 / 250000000000) = 1/(250000000000 / 355693519079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3413 : Bounds (17630427 / 50000000) (352608541 / 1000000000) (Real.log (355693519079 / 250000000000)) := by
  have h := reflection_log_3413_neg
  have he : Real.log (355693519079 / 250000000000) = -Real.log (250000000000 / 355693519079) := by
    rw [show ((355693519079 / 250000000000) : ℝ) = ((250000000000 / 355693519079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3414_neg : (14112593 / 40000000) ≤ -Real.log (250000000000 / 355766900897) ∧
    -Real.log (250000000000 / 355766900897) ≤ (176407413 / 500000000) := by
  have h := checkLog_sound (w := (105766900897 / 605766900897)) (n := 12)
    (lo := (14112593 / 40000000)) (hi := (176407413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((355766900897 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(355766900897 / 250000000000) = 1/(250000000000 / 355766900897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3414 : Bounds (14112593 / 40000000) (176407413 / 500000000) (Real.log (355766900897 / 250000000000)) := by
  have h := reflection_log_3414_neg
  have he : Real.log (355766900897 / 250000000000) = -Real.log (250000000000 / 355766900897) := by
    rw [show ((355766900897 / 250000000000) : ℝ) = ((250000000000 / 355766900897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3415_neg : (32202559 / 200000000) ≤ -Real.log (10000 / 11747) ∧
    -Real.log (10000 / 11747) ≤ (40253199 / 250000000) := by
  have h := checkLog_sound (w := (1747 / 21747)) (n := 12)
    (lo := (32202559 / 200000000)) (hi := (40253199 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11747 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11747 / 10000) = 1/(10000 / 11747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3415 : Bounds (32202559 / 200000000) (40253199 / 250000000) (Real.log (11747 / 10000)) := by
  have h := reflection_log_3415_neg
  have he : Real.log (11747 / 10000) = -Real.log (10000 / 11747) := by
    rw [show ((11747 / 10000) : ℝ) = ((10000 / 11747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3416_neg : (96004161 / 500000000) ≤ -Real.log (8253 / 10000) ∧
    -Real.log (8253 / 10000) ≤ (192008323 / 1000000000) := by
  have h := checkLog_sound (w := (1747 / 18253)) (n := 12)
    (lo := (96004161 / 500000000)) (hi := (192008323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8253) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8253) = 1/(8253 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3416 : Bounds (-192008323 / 1000000000) (-96004161 / 500000000) (Real.log (8253 / 10000)) := by
  have h := reflection_log_3416_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3417_neg : (43671 / 250000000) ≤ -Real.log (10000000 / 10001747) ∧
    -Real.log (10000000 / 10001747) ≤ (34937 / 200000000) := by
  have h := checkLog_sound (w := (1747 / 20001747)) (n := 12)
    (lo := (43671 / 250000000)) (hi := (34937 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001747 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001747 / 10000000) = 1/(10000000 / 10001747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3417 : Bounds (43671 / 250000000) (34937 / 200000000) (Real.log (10001747 / 10000000)) := by
  have h := reflection_log_3417_neg
  have he : Real.log (10001747 / 10000000) = -Real.log (10000000 / 10001747) := by
    rw [show ((10001747 / 10000000) : ℝ) = ((10000000 / 10001747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3418_neg : (34943 / 200000000) ≤ -Real.log (9998253 / 10000000) ∧
    -Real.log (9998253 / 10000000) ≤ (43679 / 250000000) := by
  have h := checkLog_sound (w := (1747 / 19998253)) (n := 12)
    (lo := (34943 / 200000000)) (hi := (43679 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998253) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998253) = 1/(9998253 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3418 : Bounds (-43679 / 250000000) (-34943 / 200000000) (Real.log (9998253 / 10000000)) := by
  have h := reflection_log_3418_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3419_neg : (84062617 / 1000000000) ≤ -Real.log (1000000 / 1087697) ∧
    -Real.log (1000000 / 1087697) ≤ (42031309 / 500000000) := by
  have h := checkLog_sound (w := (87697 / 2087697)) (n := 12)
    (lo := (84062617 / 1000000000)) (hi := (42031309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1087697 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1087697 / 1000000) = 1/(1000000 / 1087697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3419 : Bounds (84062617 / 1000000000) (42031309 / 500000000) (Real.log (1087697 / 1000000)) := by
  have h := reflection_log_3419_neg
  have he : Real.log (1087697 / 1000000) = -Real.log (1000000 / 1087697) := by
    rw [show ((1087697 / 1000000) : ℝ) = ((1000000 / 1087697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3420_neg : (91783107 / 1000000000) ≤ -Real.log (912303 / 1000000) ∧
    -Real.log (912303 / 1000000) ≤ (22945777 / 250000000) := by
  have h := checkLog_sound (w := (87697 / 1912303)) (n := 12)
    (lo := (91783107 / 1000000000)) (hi := (22945777 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 912303) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 912303) = 1/(912303 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3420 : Bounds (-22945777 / 250000000) (-91783107 / 1000000000) (Real.log (912303 / 1000000)) := by
  have h := reflection_log_3420_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3421_neg : (42134727 / 500000000) ≤ -Real.log (500000 / 543961) ∧
    -Real.log (500000 / 543961) ≤ (16853891 / 200000000) := by
  have h := checkLog_sound (w := (43961 / 1043961)) (n := 12)
    (lo := (42134727 / 500000000)) (hi := (16853891 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((543961 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(543961 / 500000) = 1/(500000 / 543961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3421 : Bounds (42134727 / 500000000) (16853891 / 200000000) (Real.log (543961 / 500000)) := by
  have h := reflection_log_3421_neg
  have he : Real.log (543961 / 500000) = -Real.log (500000 / 543961) := by
    rw [show ((543961 / 500000) : ℝ) = ((500000 / 543961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3422_neg : (46014883 / 500000000) ≤ -Real.log (456039 / 500000) ∧
    -Real.log (456039 / 500000) ≤ (92029767 / 1000000000) := by
  have h := checkLog_sound (w := (43961 / 956039)) (n := 12)
    (lo := (46014883 / 500000000)) (hi := (92029767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 456039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 456039) = 1/(456039 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3422 : Bounds (-92029767 / 1000000000) (-46014883 / 500000000) (Real.log (456039 / 500000)) := by
  have h := reflection_log_3422_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3423_neg : (7760311 / 1000000000) ≤ -Real.log (248067430479 / 250000000000) ∧
    -Real.log (248067430479 / 250000000000) ≤ (970039 / 125000000) := by
  have h := checkLog_sound (w := (1932569521 / 498067430479)) (n := 12)
    (lo := (7760311 / 1000000000)) (hi := (970039 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248067430479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248067430479) = 1/(248067430479 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3423 : Bounds (-970039 / 125000000) (-7760311 / 1000000000) (Real.log (248067430479 / 250000000000)) := by
  have h := reflection_log_3423_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3424_neg : (772049 / 100000000) ≤ -Real.log (992309236191 / 1000000000000) ∧
    -Real.log (992309236191 / 1000000000000) ≤ (7720491 / 1000000000) := by
  have h := checkLog_sound (w := (7690763809 / 1992309236191)) (n := 12)
    (lo := (772049 / 100000000)) (hi := (7720491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992309236191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992309236191) = 1/(992309236191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3424 : Bounds (-7720491 / 1000000000) (-772049 / 100000000) (Real.log (992309236191 / 1000000000000)) := by
  have h := reflection_log_3424_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3425_neg : (43961431 / 250000000) ≤ -Real.log (500000000000 / 596127054279) ∧
    -Real.log (500000000000 / 596127054279) ≤ (7033829 / 40000000) := by
  have h := checkLog_sound (w := (96127054279 / 1096127054279)) (n := 12)
    (lo := (43961431 / 250000000)) (hi := (7033829 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((596127054279 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(596127054279 / 500000000000) = 1/(500000000000 / 596127054279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3425 : Bounds (43961431 / 250000000) (7033829 / 40000000) (Real.log (596127054279 / 500000000000)) := by
  have h := reflection_log_3425_neg
  have he : Real.log (596127054279 / 500000000000) = -Real.log (500000000000 / 596127054279) := by
    rw [show ((596127054279 / 500000000000) : ℝ) = ((500000000000 / 596127054279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3426_neg : (8814961 / 50000000) ≤ -Real.log (125000000000 / 149099364309) ∧
    -Real.log (125000000000 / 149099364309) ≤ (176299221 / 1000000000) := by
  have h := checkLog_sound (w := (24099364309 / 274099364309)) (n := 12)
    (lo := (8814961 / 50000000)) (hi := (176299221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149099364309 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149099364309 / 125000000000) = 1/(125000000000 / 149099364309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3426 : Bounds (8814961 / 50000000) (176299221 / 1000000000) (Real.log (149099364309 / 125000000000)) := by
  have h := reflection_log_3426_neg
  have he : Real.log (149099364309 / 125000000000) = -Real.log (125000000000 / 149099364309) := by
    rw [show ((149099364309 / 125000000000) : ℝ) = ((125000000000 / 149099364309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3427_neg : (14112593 / 40000000) ≤ -Real.log (500000000000 / 711533801793) ∧
    -Real.log (500000000000 / 711533801793) ≤ (176407413 / 500000000) := by
  have h := checkLog_sound (w := (211533801793 / 1211533801793)) (n := 12)
    (lo := (14112593 / 40000000)) (hi := (176407413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((711533801793 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(711533801793 / 500000000000) = 1/(500000000000 / 711533801793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3427 : Bounds (14112593 / 40000000) (176407413 / 500000000) (Real.log (711533801793 / 500000000000)) := by
  have h := reflection_log_3427_neg
  have he : Real.log (711533801793 / 500000000000) = -Real.log (500000000000 / 711533801793) := by
    rw [show ((711533801793 / 500000000000) : ℝ) = ((500000000000 / 711533801793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3428_neg : (176510559 / 500000000) ≤ -Real.log (250000000000 / 355840300497) ∧
    -Real.log (250000000000 / 355840300497) ≤ (353021119 / 1000000000) := by
  have h := checkLog_sound (w := (105840300497 / 605840300497)) (n := 12)
    (lo := (176510559 / 500000000)) (hi := (353021119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((355840300497 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(355840300497 / 250000000000) = 1/(250000000000 / 355840300497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3428 : Bounds (176510559 / 500000000) (353021119 / 1000000000) (Real.log (355840300497 / 250000000000)) := by
  have h := reflection_log_3428_neg
  have he : Real.log (355840300497 / 250000000000) = -Real.log (250000000000 / 355840300497) := by
    rw [show ((355840300497 / 250000000000) : ℝ) = ((250000000000 / 355840300497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3429_neg : (503431 / 3125000) ≤ -Real.log (2500 / 2937) ∧
    -Real.log (2500 / 2937) ≤ (161097921 / 1000000000) := by
  have h := checkLog_sound (w := (437 / 5437)) (n := 12)
    (lo := (503431 / 3125000)) (hi := (161097921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2937 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2937 / 2500) = 1/(2500 / 2937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3429 : Bounds (503431 / 3125000) (161097921 / 1000000000) (Real.log (2937 / 2500)) := by
  have h := reflection_log_3429_neg
  have he : Real.log (2937 / 2500) = -Real.log (2500 / 2937) := by
    rw [show ((2937 / 2500) : ℝ) = ((2500 / 2937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3430_neg : (192129497 / 1000000000) ≤ -Real.log (2063 / 2500) ∧
    -Real.log (2063 / 2500) ≤ (96064749 / 500000000) := by
  have h := checkLog_sound (w := (437 / 4563)) (n := 12)
    (lo := (192129497 / 1000000000)) (hi := (96064749 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2063) = 1/(2063 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3430 : Bounds (-96064749 / 500000000) (-192129497 / 1000000000) (Real.log (2063 / 2500)) := by
  have h := reflection_log_3430_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3431_neg : (2731 / 15625000) ≤ -Real.log (2500000 / 2500437) ∧
    -Real.log (2500000 / 2500437) ≤ (34957 / 200000000) := by
  have h := checkLog_sound (w := (437 / 5000437)) (n := 12)
    (lo := (2731 / 15625000)) (hi := (34957 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500437 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500437 / 2500000) = 1/(2500000 / 2500437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3431 : Bounds (2731 / 15625000) (34957 / 200000000) (Real.log (2500437 / 2500000)) := by
  have h := reflection_log_3431_neg
  have he : Real.log (2500437 / 2500000) = -Real.log (2500000 / 2500437) := by
    rw [show ((2500437 / 2500000) : ℝ) = ((2500000 / 2500437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3432_neg : (34963 / 200000000) ≤ -Real.log (2499563 / 2500000) ∧
    -Real.log (2499563 / 2500000) ≤ (5463 / 31250000) := by
  have h := checkLog_sound (w := (437 / 4999563)) (n := 12)
    (lo := (34963 / 200000000)) (hi := (5463 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499563) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499563) = 1/(2499563 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3432 : Bounds (-5463 / 31250000) (-34963 / 200000000) (Real.log (2499563 / 2500000)) := by
  have h := reflection_log_3432_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3433_neg : (84109503 / 1000000000) ≤ -Real.log (250000 / 271937) ∧
    -Real.log (250000 / 271937) ≤ (1314211 / 15625000) := by
  have h := checkLog_sound (w := (21937 / 521937)) (n := 12)
    (lo := (84109503 / 1000000000)) (hi := (1314211 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((271937 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(271937 / 250000) = 1/(250000 / 271937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3433 : Bounds (84109503 / 1000000000) (1314211 / 15625000) (Real.log (271937 / 250000)) := by
  have h := reflection_log_3433_neg
  have he : Real.log (271937 / 250000) = -Real.log (250000 / 271937) := by
    rw [show ((271937 / 250000) : ℝ) = ((250000 / 271937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3434_neg : (91839011 / 1000000000) ≤ -Real.log (228063 / 250000) ∧
    -Real.log (228063 / 250000) ≤ (22959753 / 250000000) := by
  have h := checkLog_sound (w := (21937 / 478063)) (n := 12)
    (lo := (91839011 / 1000000000)) (hi := (22959753 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 228063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 228063) = 1/(228063 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3434 : Bounds (-22959753 / 250000000) (-91839011 / 1000000000) (Real.log (228063 / 250000)) := by
  have h := reflection_log_3434_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3435_neg : (84316331 / 1000000000) ≤ -Real.log (1000000 / 1087973) ∧
    -Real.log (1000000 / 1087973) ≤ (21079083 / 250000000) := by
  have h := checkLog_sound (w := (87973 / 2087973)) (n := 12)
    (lo := (84316331 / 1000000000)) (hi := (21079083 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1087973 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1087973 / 1000000) = 1/(1000000 / 1087973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3435 : Bounds (84316331 / 1000000000) (21079083 / 250000000) (Real.log (1087973 / 1000000)) := by
  have h := reflection_log_3435_neg
  have he : Real.log (1087973 / 1000000) = -Real.log (1000000 / 1087973) := by
    rw [show ((1087973 / 1000000) : ℝ) = ((1000000 / 1087973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3436_neg : (23021421 / 250000000) ≤ -Real.log (912027 / 1000000) ∧
    -Real.log (912027 / 1000000) ≤ (18417137 / 200000000) := by
  have h := checkLog_sound (w := (87973 / 1912027)) (n := 12)
    (lo := (23021421 / 250000000)) (hi := (18417137 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 912027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 912027) = 1/(912027 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3436 : Bounds (-18417137 / 200000000) (-23021421 / 250000000) (Real.log (912027 / 1000000)) := by
  have h := reflection_log_3436_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3437_neg : (971169 / 125000000) ≤ -Real.log (992260751271 / 1000000000000) ∧
    -Real.log (992260751271 / 1000000000000) ≤ (7769353 / 1000000000) := by
  have h := checkLog_sound (w := (7739248729 / 1992260751271)) (n := 12)
    (lo := (971169 / 125000000)) (hi := (7769353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992260751271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992260751271) = 1/(992260751271 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3437 : Bounds (-7769353 / 1000000000) (-971169 / 125000000) (Real.log (992260751271 / 1000000000000)) := by
  have h := reflection_log_3437_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3438_neg : (7729507 / 1000000000) ≤ -Real.log (62018768031 / 62500000000) ∧
    -Real.log (62018768031 / 62500000000) ≤ (1932377 / 250000000) := by
  have h := checkLog_sound (w := (481231969 / 124518768031)) (n := 12)
    (lo := (7729507 / 1000000000)) (hi := (1932377 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62018768031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62018768031) = 1/(62018768031 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3438 : Bounds (-1932377 / 250000000) (-7729507 / 1000000000) (Real.log (62018768031 / 62500000000)) := by
  have h := reflection_log_3438_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3439_neg : (35189703 / 200000000) ≤ -Real.log (20000000000 / 23847533357) ∧
    -Real.log (20000000000 / 23847533357) ≤ (43987129 / 250000000) := by
  have h := checkLog_sound (w := (3847533357 / 43847533357)) (n := 12)
    (lo := (35189703 / 200000000)) (hi := (43987129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23847533357 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23847533357 / 20000000000) = 1/(20000000000 / 23847533357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3439 : Bounds (35189703 / 200000000) (43987129 / 250000000) (Real.log (23847533357 / 20000000000)) := by
  have h := reflection_log_3439_neg
  have he : Real.log (23847533357 / 20000000000) = -Real.log (20000000000 / 23847533357) := by
    rw [show ((23847533357 / 20000000000) : ℝ) = ((20000000000 / 23847533357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3440_neg : (5512563 / 31250000) ≤ -Real.log (6250000000 / 7455734589) ∧
    -Real.log (6250000000 / 7455734589) ≤ (176402017 / 1000000000) := by
  have h := checkLog_sound (w := (1205734589 / 13705734589)) (n := 12)
    (lo := (5512563 / 31250000)) (hi := (176402017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7455734589 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7455734589 / 6250000000) = 1/(6250000000 / 7455734589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3440 : Bounds (5512563 / 31250000) (176402017 / 1000000000) (Real.log (7455734589 / 6250000000)) := by
  have h := reflection_log_3440_neg
  have he : Real.log (7455734589 / 6250000000) = -Real.log (6250000000 / 7455734589) := by
    rw [show ((7455734589 / 6250000000) : ℝ) = ((6250000000 / 7455734589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3441_neg : (176510559 / 500000000) ≤ -Real.log (500000000000 / 711680600993) ∧
    -Real.log (500000000000 / 711680600993) ≤ (353021119 / 1000000000) := by
  have h := checkLog_sound (w := (211680600993 / 1211680600993)) (n := 12)
    (lo := (176510559 / 500000000)) (hi := (353021119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((711680600993 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(711680600993 / 500000000000) = 1/(500000000000 / 711680600993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3441 : Bounds (176510559 / 500000000) (353021119 / 1000000000) (Real.log (711680600993 / 500000000000)) := by
  have h := reflection_log_3441_neg
  have he : Real.log (711680600993 / 500000000000) = -Real.log (500000000000 / 711680600993) := by
    rw [show ((711680600993 / 500000000000) : ℝ) = ((500000000000 / 711680600993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3442_neg : (176613709 / 500000000) ≤ -Real.log (250000000000 / 355913717887) ∧
    -Real.log (250000000000 / 355913717887) ≤ (353227419 / 1000000000) := by
  have h := checkLog_sound (w := (105913717887 / 605913717887)) (n := 12)
    (lo := (176613709 / 500000000)) (hi := (353227419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((355913717887 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(355913717887 / 250000000000) = 1/(250000000000 / 355913717887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3442 : Bounds (176613709 / 500000000) (353227419 / 1000000000) (Real.log (355913717887 / 250000000000)) := by
  have h := reflection_log_3442_neg
  have he : Real.log (355913717887 / 250000000000) = -Real.log (250000000000 / 355913717887) := by
    rw [show ((355913717887 / 250000000000) : ℝ) = ((250000000000 / 355913717887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3443_neg : (161183037 / 1000000000) ≤ -Real.log (10000 / 11749) ∧
    -Real.log (10000 / 11749) ≤ (80591519 / 500000000) := by
  have h := checkLog_sound (w := (1749 / 21749)) (n := 12)
    (lo := (161183037 / 1000000000)) (hi := (80591519 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11749 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11749 / 10000) = 1/(10000 / 11749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3443 : Bounds (161183037 / 1000000000) (80591519 / 500000000) (Real.log (11749 / 10000)) := by
  have h := reflection_log_3443_neg
  have he : Real.log (11749 / 10000) = -Real.log (10000 / 11749) := by
    rw [show ((11749 / 10000) : ℝ) = ((10000 / 11749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3444_neg : (192250687 / 1000000000) ≤ -Real.log (8251 / 10000) ∧
    -Real.log (8251 / 10000) ≤ (3003917 / 15625000) := by
  have h := checkLog_sound (w := (1749 / 18251)) (n := 12)
    (lo := (192250687 / 1000000000)) (hi := (3003917 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8251) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8251) = 1/(8251 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3444 : Bounds (-3003917 / 15625000) (-192250687 / 1000000000) (Real.log (8251 / 10000)) := by
  have h := reflection_log_3444_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3445_neg : (43721 / 250000000) ≤ -Real.log (10000000 / 10001749) ∧
    -Real.log (10000000 / 10001749) ≤ (34977 / 200000000) := by
  have h := checkLog_sound (w := (1749 / 20001749)) (n := 12)
    (lo := (43721 / 250000000)) (hi := (34977 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001749 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001749 / 10000000) = 1/(10000000 / 10001749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3445 : Bounds (43721 / 250000000) (34977 / 200000000) (Real.log (10001749 / 10000000)) := by
  have h := reflection_log_3445_neg
  have he : Real.log (10001749 / 10000000) = -Real.log (10000000 / 10001749) := by
    rw [show ((10001749 / 10000000) : ℝ) = ((10000000 / 10001749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3446_neg : (34983 / 200000000) ≤ -Real.log (9998251 / 10000000) ∧
    -Real.log (9998251 / 10000000) ≤ (43729 / 250000000) := by
  have h := checkLog_sound (w := (1749 / 19998251)) (n := 12)
    (lo := (34983 / 200000000)) (hi := (43729 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998251) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998251) = 1/(9998251 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3446 : Bounds (-43729 / 250000000) (-34983 / 200000000) (Real.log (9998251 / 10000000)) := by
  have h := reflection_log_3446_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3447_neg : (21039097 / 250000000) ≤ -Real.log (1000000 / 1087799) ∧
    -Real.log (1000000 / 1087799) ≤ (84156389 / 1000000000) := by
  have h := checkLog_sound (w := (87799 / 2087799)) (n := 12)
    (lo := (21039097 / 250000000)) (hi := (84156389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1087799 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1087799 / 1000000) = 1/(1000000 / 1087799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3447 : Bounds (21039097 / 250000000) (84156389 / 1000000000) (Real.log (1087799 / 1000000)) := by
  have h := reflection_log_3447_neg
  have he : Real.log (1087799 / 1000000) = -Real.log (1000000 / 1087799) := by
    rw [show ((1087799 / 1000000) : ℝ) = ((1000000 / 1087799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3448_neg : (45947459 / 500000000) ≤ -Real.log (912201 / 1000000) ∧
    -Real.log (912201 / 1000000) ≤ (91894919 / 1000000000) := by
  have h := checkLog_sound (w := (87799 / 1912201)) (n := 12)
    (lo := (45947459 / 500000000)) (hi := (91894919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 912201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 912201) = 1/(912201 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3448 : Bounds (-91894919 / 1000000000) (-45947459 / 500000000) (Real.log (912201 / 1000000)) := by
  have h := reflection_log_3448_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3449_neg : (84363207 / 1000000000) ≤ -Real.log (125000 / 136003) ∧
    -Real.log (125000 / 136003) ≤ (10545401 / 125000000) := by
  have h := checkLog_sound (w := (11003 / 261003)) (n := 12)
    (lo := (84363207 / 1000000000)) (hi := (10545401 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((136003 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(136003 / 125000) = 1/(125000 / 136003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3449 : Bounds (84363207 / 1000000000) (10545401 / 125000000) (Real.log (136003 / 125000)) := by
  have h := reflection_log_3449_neg
  have he : Real.log (136003 / 125000) = -Real.log (125000 / 136003) := by
    rw [show ((136003 / 125000) : ℝ) = ((125000 / 136003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3450_neg : (18428321 / 200000000) ≤ -Real.log (113997 / 125000) ∧
    -Real.log (113997 / 125000) ≤ (46070803 / 500000000) := by
  have h := checkLog_sound (w := (11003 / 238997)) (n := 12)
    (lo := (18428321 / 200000000)) (hi := (46070803 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 113997) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 113997) = 1/(113997 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3450 : Bounds (-46070803 / 500000000) (-18428321 / 200000000) (Real.log (113997 / 125000)) := by
  have h := reflection_log_3450_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3451_neg : (3889199 / 500000000) ≤ -Real.log (15503933991 / 15625000000) ∧
    -Real.log (15503933991 / 15625000000) ≤ (7778399 / 1000000000) := by
  have h := checkLog_sound (w := (121066009 / 31128933991)) (n := 12)
    (lo := (3889199 / 500000000)) (hi := (7778399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15503933991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15503933991) = 1/(15503933991 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3451 : Bounds (-7778399 / 1000000000) (-3889199 / 500000000) (Real.log (15503933991 / 15625000000)) := by
  have h := reflection_log_3451_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3452_neg : (7738529 / 1000000000) ≤ -Real.log (992291335599 / 1000000000000) ∧
    -Real.log (992291335599 / 1000000000000) ≤ (773853 / 100000000) := by
  have h := checkLog_sound (w := (7708664401 / 1992291335599)) (n := 12)
    (lo := (7738529 / 1000000000)) (hi := (773853 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992291335599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992291335599) = 1/(992291335599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3452 : Bounds (-773853 / 100000000) (-7738529 / 1000000000) (Real.log (992291335599 / 1000000000000)) := by
  have h := reflection_log_3452_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3453_neg : (176051307 / 1000000000) ≤ -Real.log (500000000000 / 596249620423) ∧
    -Real.log (500000000000 / 596249620423) ≤ (44012827 / 250000000) := by
  have h := checkLog_sound (w := (96249620423 / 1096249620423)) (n := 12)
    (lo := (176051307 / 1000000000)) (hi := (44012827 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((596249620423 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(596249620423 / 500000000000) = 1/(500000000000 / 596249620423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3453 : Bounds (176051307 / 1000000000) (44012827 / 250000000) (Real.log (596249620423 / 500000000000)) := by
  have h := reflection_log_3453_neg
  have he : Real.log (596249620423 / 500000000000) = -Real.log (500000000000 / 596249620423) := by
    rw [show ((596249620423 / 500000000000) : ℝ) = ((500000000000 / 596249620423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3454_neg : (44126203 / 250000000) ≤ -Real.log (250000000000 / 298260041931) ∧
    -Real.log (250000000000 / 298260041931) ≤ (176504813 / 1000000000) := by
  have h := checkLog_sound (w := (48260041931 / 548260041931)) (n := 12)
    (lo := (44126203 / 250000000)) (hi := (176504813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298260041931 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298260041931 / 250000000000) = 1/(250000000000 / 298260041931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3454 : Bounds (44126203 / 250000000) (176504813 / 1000000000) (Real.log (298260041931 / 250000000000)) := by
  have h := reflection_log_3454_neg
  have he : Real.log (298260041931 / 250000000000) = -Real.log (250000000000 / 298260041931) := by
    rw [show ((298260041931 / 250000000000) : ℝ) = ((250000000000 / 298260041931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3455_neg : (176613709 / 500000000) ≤ -Real.log (500000000000 / 711827435773) ∧
    -Real.log (500000000000 / 711827435773) ≤ (353227419 / 1000000000) := by
  have h := checkLog_sound (w := (211827435773 / 1211827435773)) (n := 12)
    (lo := (176613709 / 500000000)) (hi := (353227419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((711827435773 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(711827435773 / 500000000000) = 1/(500000000000 / 711827435773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3455 : Bounds (176613709 / 500000000) (353227419 / 1000000000) (Real.log (711827435773 / 500000000000)) := by
  have h := reflection_log_3455_neg
  have he : Real.log (711827435773 / 500000000000) = -Real.log (500000000000 / 711827435773) := by
    rw [show ((711827435773 / 500000000000) : ℝ) = ((500000000000 / 711827435773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


