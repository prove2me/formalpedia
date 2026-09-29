-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0226__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0226__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T22:01:28.465891+00:00
-- url     : https://prove2.me/theorems/146862be-a192-467e-8fdd-3736faa3ed45
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0226 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0227, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0226 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0227, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0228)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0226 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0227, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0228)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0226 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0227, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0228) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0226 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0227, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0228).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0226 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_14464_neg : (11843837 / 3906250) ≤ -Real.log (500000000000 / 10369565217391) ∧
    -Real.log (500000000000 / 10369565217391) ≤ (3032022277 / 1000000000) := by
  have h := checkLog_sound (w := (2369565217391 / 18369565217391)) (n := 12)
    (lo := (16214597 / 62500000)) (hi := (259433553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10369565217391 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(10369565217391 / 8000000000000) = 1/(500000000000 / 10369565217391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14464 : Bounds (11843837 / 3906250) (3032022277 / 1000000000) (Real.log (10369565217391 / 500000000000)) := by
  have h := reflection_log_14464_neg
  have he : Real.log (10369565217391 / 500000000000) = -Real.log (500000000000 / 10369565217391) := by
    rw [show ((10369565217391 / 500000000000) : ℝ) = ((500000000000 / 10369565217391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14465_neg : (766686393 / 250000000) ≤ -Real.log (25000000000 / 536797752809) ∧
    -Real.log (25000000000 / 536797752809) ≤ (3066745577 / 1000000000) := by
  have h := checkLog_sound (w := (136797752809 / 936797752809)) (n := 12)
    (lo := (73539213 / 250000000)) (hi := (294156853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((536797752809 / 400000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(536797752809 / 400000000000) = 1/(25000000000 / 536797752809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14465 : Bounds (766686393 / 250000000) (3066745577 / 1000000000) (Real.log (536797752809 / 25000000000)) := by
  have h := reflection_log_14465_neg
  have he : Real.log (536797752809 / 25000000000) = -Real.log (25000000000 / 536797752809) := by
    rw [show ((536797752809 / 25000000000) : ℝ) = ((25000000000 / 536797752809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14466_neg : (649195293 / 1000000000) ≤ -Real.log (500 / 957) ∧
    -Real.log (500 / 957) ≤ (324597647 / 500000000) := by
  have h := checkLog_sound (w := (457 / 1457)) (n := 12)
    (lo := (649195293 / 1000000000)) (hi := (324597647 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((957 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(957 / 500) = 1/(500 / 957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14466 : Bounds (649195293 / 1000000000) (324597647 / 500000000) (Real.log (957 / 500)) := by
  have h := reflection_log_14466_neg
  have he : Real.log (957 / 500) = -Real.log (500 / 957) := by
    rw [show ((957 / 500) : ℝ) = ((500 / 957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14467_neg : (2453407981 / 1000000000) ≤ -Real.log (43 / 500) ∧
    -Real.log (43 / 500) ≤ (490681597 / 200000000) := by
  have h := checkLog_sound (w := (39 / 211)) (n := 12)
    (lo := (373966441 / 1000000000)) (hi := (186983221 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 86) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125 / 86) = 1/(43 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14467 : Bounds (-490681597 / 200000000) (-2453407981 / 1000000000) (Real.log (43 / 500)) := by
  have h := reflection_log_14467_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14468_neg : (456791 / 500000000) ≤ -Real.log (500000 / 500457) ∧
    -Real.log (500000 / 500457) ≤ (913583 / 1000000000) := by
  have h := checkLog_sound (w := (457 / 1000457)) (n := 12)
    (lo := (456791 / 500000000)) (hi := (913583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500457 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500457 / 500000) = 1/(500000 / 500457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14468 : Bounds (456791 / 500000000) (913583 / 1000000000) (Real.log (500457 / 500000)) := by
  have h := reflection_log_14468_neg
  have he : Real.log (500457 / 500000) = -Real.log (500000 / 500457) := by
    rw [show ((500457 / 500000) : ℝ) = ((500000 / 500457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14469_neg : (914417 / 1000000000) ≤ -Real.log (499543 / 500000) ∧
    -Real.log (499543 / 500000) ≤ (457209 / 500000000) := by
  have h := checkLog_sound (w := (457 / 999543)) (n := 12)
    (lo := (914417 / 1000000000)) (hi := (457209 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499543) = 1/(499543 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14469 : Bounds (-457209 / 500000000) (-914417 / 1000000000) (Real.log (499543 / 500000)) := by
  have h := reflection_log_14469_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14470_neg : (440001147 / 1000000000) ≤ -Real.log (1000000 / 1552709) ∧
    -Real.log (1000000 / 1552709) ≤ (110000287 / 250000000) := by
  have h := checkLog_sound (w := (552709 / 2552709)) (n := 12)
    (lo := (440001147 / 1000000000)) (hi := (110000287 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1552709 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1552709 / 1000000) = 1/(1000000 / 1552709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14470 : Bounds (440001147 / 1000000000) (110000287 / 250000000) (Real.log (1552709 / 1000000)) := by
  have h := reflection_log_14470_neg
  have he : Real.log (1552709 / 1000000) = -Real.log (1000000 / 1552709) := by
    rw [show ((1552709 / 1000000) : ℝ) = ((1000000 / 1552709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14471_neg : (25142059 / 31250000) ≤ -Real.log (447291 / 1000000) ∧
    -Real.log (447291 / 1000000) ≤ (80454589 / 100000000) := by
  have h := checkLog_sound (w := (52709 / 947291)) (n := 12)
    (lo := (27849677 / 250000000)) (hi := (111398709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 447291) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 447291) = 1/(447291 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14471 : Bounds (-80454589 / 100000000) (-25142059 / 31250000) (Real.log (447291 / 1000000)) := by
  have h := reflection_log_14471_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14472_neg : (55285849 / 125000000) ≤ -Real.log (500000 / 778131) ∧
    -Real.log (500000 / 778131) ≤ (442286793 / 1000000000) := by
  have h := checkLog_sound (w := (278131 / 1278131)) (n := 12)
    (lo := (55285849 / 125000000)) (hi := (442286793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((778131 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(778131 / 500000) = 1/(500000 / 778131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14472 : Bounds (55285849 / 125000000) (442286793 / 1000000000) (Real.log (778131 / 500000)) := by
  have h := reflection_log_14472_neg
  have he : Real.log (778131 / 500000) = -Real.log (500000 / 778131) := by
    rw [show ((778131 / 500000) : ℝ) = ((500000 / 778131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14473_neg : (40626049 / 50000000) ≤ -Real.log (221869 / 500000) ∧
    -Real.log (221869 / 500000) ≤ (406260491 / 500000000) := by
  have h := checkLog_sound (w := (28131 / 471869)) (n := 12)
    (lo := (596869 / 5000000)) (hi := (119373801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 221869) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 221869) = 1/(221869 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14473 : Bounds (-406260491 / 500000000) (-40626049 / 50000000) (Real.log (221869 / 500000)) := by
  have h := reflection_log_14473_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14474_neg : (92558547 / 250000000) ≤ -Real.log (172643146839 / 250000000000) ∧
    -Real.log (172643146839 / 250000000000) ≤ (370234189 / 1000000000) := by
  have h := checkLog_sound (w := (77356853161 / 422643146839)) (n := 12)
    (lo := (92558547 / 250000000)) (hi := (370234189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 172643146839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 172643146839) = 1/(172643146839 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14474 : Bounds (-370234189 / 1000000000) (-92558547 / 250000000) (Real.log (172643146839 / 250000000000)) := by
  have h := reflection_log_14474_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14475_neg : (182272371 / 500000000) ≤ -Real.log (694512761319 / 1000000000000) ∧
    -Real.log (694512761319 / 1000000000000) ≤ (364544743 / 1000000000) := by
  have h := checkLog_sound (w := (305487238681 / 1694512761319)) (n := 12)
    (lo := (182272371 / 500000000)) (hi := (364544743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 694512761319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 694512761319) = 1/(694512761319 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14475 : Bounds (-364544743 / 1000000000) (-182272371 / 500000000) (Real.log (694512761319 / 1000000000000)) := by
  have h := reflection_log_14475_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14476_neg : (311136759 / 250000000) ≤ -Real.log (250000000000 / 867840510987) ∧
    -Real.log (250000000000 / 867840510987) ≤ (622273519 / 500000000) := by
  have h := checkLog_sound (w := (367840510987 / 1367840510987)) (n := 12)
    (lo := (34462491 / 62500000)) (hi := (551399857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((867840510987 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(867840510987 / 500000000000) = 1/(250000000000 / 867840510987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14476 : Bounds (311136759 / 250000000) (622273519 / 500000000) (Real.log (867840510987 / 250000000000)) := by
  have h := reflection_log_14476_neg
  have he : Real.log (867840510987 / 250000000000) = -Real.log (250000000000 / 867840510987) := by
    rw [show ((867840510987 / 250000000000) : ℝ) = ((250000000000 / 867840510987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14477_neg : (313701943 / 250000000) ≤ -Real.log (500000000000 / 1753582068699) ∧
    -Real.log (500000000000 / 1753582068699) ≤ (627403887 / 500000000) := by
  have h := checkLog_sound (w := (753582068699 / 2753582068699)) (n := 12)
    (lo := (35103787 / 62500000)) (hi := (561660593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1753582068699 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1753582068699 / 1000000000000) = 1/(500000000000 / 1753582068699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14477 : Bounds (313701943 / 250000000) (627403887 / 500000000) (Real.log (1753582068699 / 500000000000)) := by
  have h := reflection_log_14477_neg
  have he : Real.log (1753582068699 / 500000000000) = -Real.log (500000000000 / 1753582068699) := by
    rw [show ((1753582068699 / 500000000000) : ℝ) = ((500000000000 / 1753582068699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14478_neg : (766686393 / 250000000) ≤ -Real.log (500000000000 / 10735955056179) ∧
    -Real.log (500000000000 / 10735955056179) ≤ (3066745577 / 1000000000) := by
  have h := checkLog_sound (w := (2735955056179 / 18735955056179)) (n := 12)
    (lo := (73539213 / 250000000)) (hi := (294156853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10735955056179 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(10735955056179 / 8000000000000) = 1/(500000000000 / 10735955056179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14478 : Bounds (766686393 / 250000000) (3066745577 / 1000000000) (Real.log (10735955056179 / 500000000000)) := by
  have h := reflection_log_14478_neg
  have he : Real.log (10735955056179 / 500000000000) = -Real.log (500000000000 / 10735955056179) := by
    rw [show ((10735955056179 / 500000000000) : ℝ) = ((500000000000 / 10735955056179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14479_neg : (3102603273 / 1000000000) ≤ -Real.log (100000000000 / 2225581395349) ∧
    -Real.log (100000000000 / 2225581395349) ≤ (1551301639 / 500000000) := by
  have h := checkLog_sound (w := (625581395349 / 3825581395349)) (n := 12)
    (lo := (330014553 / 1000000000)) (hi := (165007277 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2225581395349 / 1600000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2225581395349 / 1600000000000) = 1/(100000000000 / 2225581395349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14479 : Bounds (3102603273 / 1000000000) (1551301639 / 500000000) (Real.log (2225581395349 / 100000000000)) := by
  have h := reflection_log_14479_neg
  have he : Real.log (2225581395349 / 100000000000) = -Real.log (100000000000 / 2225581395349) := by
    rw [show ((2225581395349 / 100000000000) : ℝ) = ((100000000000 / 2225581395349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14480_neg : (81345183 / 125000000) ≤ -Real.log (1000 / 1917) ∧
    -Real.log (1000 / 1917) ≤ (130152293 / 200000000) := by
  have h := checkLog_sound (w := (917 / 2917)) (n := 12)
    (lo := (81345183 / 125000000)) (hi := (130152293 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1917 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1917 / 1000) = 1/(1000 / 1917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14480 : Bounds (81345183 / 125000000) (130152293 / 200000000) (Real.log (1917 / 1000)) := by
  have h := reflection_log_14480_neg
  have he : Real.log (1917 / 1000) = -Real.log (1000 / 1917) := by
    rw [show ((1917 / 1000) : ℝ) = ((1000 / 1917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14481_neg : (2488914669 / 1000000000) ≤ -Real.log (83 / 1000) ∧
    -Real.log (83 / 1000) ≤ (2488914673 / 1000000000) := by
  have h := checkLog_sound (w := (21 / 104)) (n := 12)
    (lo := (409473129 / 1000000000)) (hi := (40947313 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 83) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125 / 83) = 1/(83 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14481 : Bounds (-2488914673 / 1000000000) (-2488914669 / 1000000000) (Real.log (83 / 1000)) := by
  have h := reflection_log_14481_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14482_neg : (916579 / 1000000000) ≤ -Real.log (1000000 / 1000917) ∧
    -Real.log (1000000 / 1000917) ≤ (45829 / 50000000) := by
  have h := checkLog_sound (w := (917 / 2000917)) (n := 12)
    (lo := (916579 / 1000000000)) (hi := (45829 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000917 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000917 / 1000000) = 1/(1000000 / 1000917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14482 : Bounds (916579 / 1000000000) (45829 / 50000000) (Real.log (1000917 / 1000000)) := by
  have h := reflection_log_14482_neg
  have he : Real.log (1000917 / 1000000) = -Real.log (1000000 / 1000917) := by
    rw [show ((1000917 / 1000000) : ℝ) = ((1000000 / 1000917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14483_neg : (45871 / 50000000) ≤ -Real.log (999083 / 1000000) ∧
    -Real.log (999083 / 1000000) ≤ (917421 / 1000000000) := by
  have h := checkLog_sound (w := (917 / 1999083)) (n := 12)
    (lo := (45871 / 50000000)) (hi := (917421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999083) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999083) = 1/(999083 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14483 : Bounds (-917421 / 1000000000) (-45871 / 50000000) (Real.log (999083 / 1000000)) := by
  have h := reflection_log_14483_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14484_neg : (220927447 / 500000000) ≤ -Real.log (100000 / 155559) ∧
    -Real.log (100000 / 155559) ≤ (88370979 / 200000000) := by
  have h := checkLog_sound (w := (55559 / 255559)) (n := 12)
    (lo := (220927447 / 500000000)) (hi := (88370979 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((155559 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(155559 / 100000) = 1/(100000 / 155559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14484 : Bounds (220927447 / 500000000) (88370979 / 200000000) (Real.log (155559 / 100000)) := by
  have h := reflection_log_14484_neg
  have he : Real.log (155559 / 100000) = -Real.log (100000 / 155559) := by
    rw [show ((155559 / 100000) : ℝ) = ((100000 / 155559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14485_neg : (405503859 / 500000000) ≤ -Real.log (44441 / 100000) ∧
    -Real.log (44441 / 100000) ≤ (20275193 / 25000000) := by
  have h := checkLog_sound (w := (5559 / 94441)) (n := 12)
    (lo := (58930269 / 500000000)) (hi := (117860539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 44441) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 44441) = 1/(44441 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14485 : Bounds (-20275193 / 25000000) (-405503859 / 500000000) (Real.log (44441 / 100000)) := by
  have h := reflection_log_14485_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14486_neg : (222075531 / 500000000) ≤ -Real.log (500000 / 779583) ∧
    -Real.log (500000 / 779583) ≤ (444151063 / 1000000000) := by
  have h := checkLog_sound (w := (279583 / 1279583)) (n := 12)
    (lo := (222075531 / 500000000)) (hi := (444151063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((779583 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(779583 / 500000) = 1/(500000 / 779583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14486 : Bounds (222075531 / 500000000) (444151063 / 1000000000) (Real.log (779583 / 500000)) := by
  have h := reflection_log_14486_neg
  have he : Real.log (779583 / 500000) = -Real.log (500000 / 779583) := by
    rw [show ((779583 / 500000) : ℝ) = ((500000 / 779583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14487_neg : (819086891 / 1000000000) ≤ -Real.log (220417 / 500000) ∧
    -Real.log (220417 / 500000) ≤ (819086893 / 1000000000) := by
  have h := checkLog_sound (w := (29583 / 470417)) (n := 12)
    (lo := (125939711 / 1000000000)) (hi := (245976 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 220417) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 220417) = 1/(220417 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14487 : Bounds (-819086893 / 1000000000) (-819086891 / 1000000000) (Real.log (220417 / 500000)) := by
  have h := reflection_log_14487_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14488_neg : (93733957 / 250000000) ≤ -Real.log (171833346111 / 250000000000) ∧
    -Real.log (171833346111 / 250000000000) ≤ (374935829 / 1000000000) := by
  have h := checkLog_sound (w := (78166653889 / 421833346111)) (n := 12)
    (lo := (93733957 / 250000000)) (hi := (374935829 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 171833346111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 171833346111) = 1/(171833346111 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14488 : Bounds (-374935829 / 1000000000) (-93733957 / 250000000) (Real.log (171833346111 / 250000000000)) := by
  have h := reflection_log_14488_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14489_neg : (46144103 / 125000000) ≤ -Real.log (6913197519 / 10000000000) ∧
    -Real.log (6913197519 / 10000000000) ≤ (14766113 / 40000000) := by
  have h := checkLog_sound (w := (3086802481 / 16913197519)) (n := 12)
    (lo := (46144103 / 125000000)) (hi := (14766113 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 6913197519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 6913197519) = 1/(6913197519 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14489 : Bounds (-14766113 / 40000000) (-46144103 / 125000000) (Real.log (6913197519 / 10000000000)) := by
  have h := reflection_log_14489_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14490_neg : (1252862613 / 1000000000) ≤ -Real.log (100000000000 / 350034877703) ∧
    -Real.log (100000000000 / 350034877703) ≤ (250572523 / 200000000) := by
  have h := checkLog_sound (w := (150034877703 / 550034877703)) (n := 12)
    (lo := (559715433 / 1000000000)) (hi := (279857717 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((350034877703 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(350034877703 / 200000000000) = 1/(100000000000 / 350034877703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14490 : Bounds (1252862613 / 1000000000) (250572523 / 200000000) (Real.log (350034877703 / 100000000000)) := by
  have h := reflection_log_14490_neg
  have he : Real.log (350034877703 / 100000000000) = -Real.log (100000000000 / 350034877703) := by
    rw [show ((350034877703 / 100000000000) : ℝ) = ((100000000000 / 350034877703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14491_neg : (1263237953 / 1000000000) ≤ -Real.log (500000000000 / 1768427571377) ∧
    -Real.log (500000000000 / 1768427571377) ≤ (252647591 / 200000000) := by
  have h := checkLog_sound (w := (768427571377 / 2768427571377)) (n := 12)
    (lo := (570090773 / 1000000000)) (hi := (285045387 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1768427571377 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1768427571377 / 1000000000000) = 1/(500000000000 / 1768427571377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14491 : Bounds (1263237953 / 1000000000) (252647591 / 200000000) (Real.log (1768427571377 / 500000000000)) := by
  have h := reflection_log_14491_neg
  have he : Real.log (1768427571377 / 500000000000) = -Real.log (500000000000 / 1768427571377) := by
    rw [show ((1768427571377 / 500000000000) : ℝ) = ((500000000000 / 1768427571377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14492_neg : (3102603273 / 1000000000) ≤ -Real.log (62500000000 / 1390988372093) ∧
    -Real.log (62500000000 / 1390988372093) ≤ (1551301639 / 500000000) := by
  have h := checkLog_sound (w := (390988372093 / 2390988372093)) (n := 12)
    (lo := (330014553 / 1000000000)) (hi := (165007277 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1390988372093 / 1000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1390988372093 / 1000000000000) = 1/(62500000000 / 1390988372093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14492 : Bounds (3102603273 / 1000000000) (1551301639 / 500000000) (Real.log (1390988372093 / 62500000000)) := by
  have h := reflection_log_14492_neg
  have he : Real.log (1390988372093 / 62500000000) = -Real.log (62500000000 / 1390988372093) := by
    rw [show ((1390988372093 / 62500000000) : ℝ) = ((62500000000 / 1390988372093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14493_neg : (3139676133 / 1000000000) ≤ -Real.log (100000000000 / 2309638554217) ∧
    -Real.log (100000000000 / 2309638554217) ≤ (1569838069 / 500000000) := by
  have h := checkLog_sound (w := (709638554217 / 3909638554217)) (n := 12)
    (lo := (367087413 / 1000000000)) (hi := (183543707 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2309638554217 / 1600000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2309638554217 / 1600000000000) = 1/(100000000000 / 2309638554217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14493 : Bounds (3139676133 / 1000000000) (1569838069 / 500000000) (Real.log (2309638554217 / 100000000000)) := by
  have h := reflection_log_14493_neg
  have he : Real.log (2309638554217 / 100000000000) = -Real.log (100000000000 / 2309638554217) := by
    rw [show ((2309638554217 / 100000000000) : ℝ) = ((100000000000 / 2309638554217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14494_neg : (326162593 / 500000000) ≤ -Real.log (25 / 48) ∧
    -Real.log (25 / 48) ≤ (652325187 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 73)) (n := 12)
    (lo := (326162593 / 500000000)) (hi := (652325187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48 / 25) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48 / 25) = 1/(25 / 48) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14494 : Bounds (326162593 / 500000000) (652325187 / 1000000000) (Real.log (48 / 25)) := by
  have h := reflection_log_14494_neg
  have he : Real.log (48 / 25) = -Real.log (25 / 48) := by
    rw [show ((48 / 25) : ℝ) = ((25 / 48) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14495_neg : (1262864321 / 500000000) ≤ -Real.log (2 / 25) ∧
    -Real.log (2 / 25) ≤ (1262864323 / 500000000) := by
  have h := checkLog_sound (w := (9 / 41)) (n := 12)
    (lo := (223143551 / 500000000)) (hi := (446287103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 16) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(25 / 16) = 1/(2 / 25) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14495 : Bounds (-1262864323 / 500000000) (-1262864321 / 500000000) (Real.log (2 / 25)) := by
  have h := reflection_log_14495_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14496_neg : (919577 / 1000000000) ≤ -Real.log (25000 / 25023) ∧
    -Real.log (25000 / 25023) ≤ (459789 / 500000000) := by
  have h := checkLog_sound (w := (23 / 50023)) (n := 12)
    (lo := (919577 / 1000000000)) (hi := (459789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25023 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25023 / 25000) = 1/(25000 / 25023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14496 : Bounds (919577 / 1000000000) (459789 / 500000000) (Real.log (25023 / 25000)) := by
  have h := reflection_log_14496_neg
  have he : Real.log (25023 / 25000) = -Real.log (25000 / 25023) := by
    rw [show ((25023 / 25000) : ℝ) = ((25000 / 25023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14497_neg : (920423 / 1000000000) ≤ -Real.log (24977 / 25000) ∧
    -Real.log (24977 / 25000) ≤ (115053 / 125000000) := by
  have h := checkLog_sound (w := (23 / 49977)) (n := 12)
    (lo := (920423 / 1000000000)) (hi := (115053 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 24977) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 24977) = 1/(24977 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14497 : Bounds (-115053 / 125000000) (-920423 / 1000000000) (Real.log (24977 / 25000)) := by
  have h := reflection_log_14497_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14498_neg : (110930153 / 250000000) ≤ -Real.log (200000 / 311699) ∧
    -Real.log (200000 / 311699) ≤ (443720613 / 1000000000) := by
  have h := checkLog_sound (w := (111699 / 511699)) (n := 12)
    (lo := (110930153 / 250000000)) (hi := (443720613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((311699 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(311699 / 200000) = 1/(200000 / 311699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14498 : Bounds (110930153 / 250000000) (443720613 / 1000000000) (Real.log (311699 / 200000)) := by
  have h := reflection_log_14498_neg
  have he : Real.log (311699 / 200000) = -Real.log (200000 / 311699) := by
    rw [show ((311699 / 200000) : ℝ) = ((200000 / 311699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14499_neg : (817565933 / 1000000000) ≤ -Real.log (88301 / 200000) ∧
    -Real.log (88301 / 200000) ≤ (163513187 / 200000000) := by
  have h := checkLog_sound (w := (11699 / 188301)) (n := 12)
    (lo := (124418753 / 1000000000)) (hi := (62209377 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 88301) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 88301) = 1/(88301 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14499 : Bounds (-163513187 / 200000000) (-817565933 / 1000000000) (Real.log (88301 / 200000)) := by
  have h := reflection_log_14499_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14500_neg : (446028509 / 1000000000) ≤ -Real.log (62500 / 97631) ∧
    -Real.log (62500 / 97631) ≤ (44602851 / 100000000) := by
  have h := checkLog_sound (w := (35131 / 160131)) (n := 12)
    (lo := (446028509 / 1000000000)) (hi := (44602851 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((97631 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(97631 / 62500) = 1/(62500 / 97631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14500 : Bounds (446028509 / 1000000000) (44602851 / 100000000) (Real.log (97631 / 62500)) := by
  have h := reflection_log_14500_neg
  have he : Real.log (97631 / 62500) = -Real.log (62500 / 97631) := by
    rw [show ((97631 / 62500) : ℝ) = ((62500 / 97631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14501_neg : (82575557 / 100000000) ≤ -Real.log (27369 / 62500) ∧
    -Real.log (27369 / 62500) ≤ (206438893 / 250000000) := by
  have h := checkLog_sound (w := (3881 / 58619)) (n := 12)
    (lo := (13260839 / 100000000)) (hi := (132608391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 27369) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31250 / 27369) = 1/(27369 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14501 : Bounds (-206438893 / 250000000) (-82575557 / 100000000) (Real.log (27369 / 62500)) := by
  have h := reflection_log_14501_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14502_neg : (379727061 / 1000000000) ≤ -Real.log (2672062839 / 3906250000) ∧
    -Real.log (2672062839 / 3906250000) ≤ (189863531 / 500000000) := by
  have h := checkLog_sound (w := (1234187161 / 6578312839)) (n := 12)
    (lo := (379727061 / 1000000000)) (hi := (189863531 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 2672062839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 2672062839) = 1/(2672062839 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14502 : Bounds (-189863531 / 500000000) (-379727061 / 1000000000) (Real.log (2672062839 / 3906250000)) := by
  have h := reflection_log_14502_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14503_neg : (373845321 / 1000000000) ≤ -Real.log (27523333399 / 40000000000) ∧
    -Real.log (27523333399 / 40000000000) ≤ (186922661 / 500000000) := by
  have h := checkLog_sound (w := (12476666601 / 67523333399)) (n := 12)
    (lo := (373845321 / 1000000000)) (hi := (186922661 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 27523333399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 27523333399) = 1/(27523333399 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14503 : Bounds (-186922661 / 500000000) (-373845321 / 1000000000) (Real.log (27523333399 / 40000000000)) := by
  have h := reflection_log_14503_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14504_neg : (252257309 / 200000000) ≤ -Real.log (500000000000 / 1764980011551) ∧
    -Real.log (500000000000 / 1764980011551) ≤ (1261286547 / 1000000000) := by
  have h := checkLog_sound (w := (764980011551 / 2764980011551)) (n := 12)
    (lo := (113627873 / 200000000)) (hi := (284069683 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1764980011551 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1764980011551 / 1000000000000) = 1/(500000000000 / 1764980011551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14504 : Bounds (252257309 / 200000000) (1261286547 / 1000000000) (Real.log (1764980011551 / 500000000000)) := by
  have h := reflection_log_14504_neg
  have he : Real.log (1764980011551 / 500000000000) = -Real.log (500000000000 / 1764980011551) := by
    rw [show ((1764980011551 / 500000000000) : ℝ) = ((500000000000 / 1764980011551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14505_neg : (1271784079 / 1000000000) ≤ -Real.log (250000000000 / 891802769557) ∧
    -Real.log (250000000000 / 891802769557) ≤ (1271784081 / 1000000000) := by
  have h := checkLog_sound (w := (391802769557 / 1391802769557)) (n := 12)
    (lo := (578636899 / 1000000000)) (hi := (5786369 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((891802769557 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(891802769557 / 500000000000) = 1/(250000000000 / 891802769557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14505 : Bounds (1271784079 / 1000000000) (1271784081 / 1000000000) (Real.log (891802769557 / 250000000000)) := by
  have h := reflection_log_14505_neg
  have he : Real.log (891802769557 / 250000000000) = -Real.log (250000000000 / 891802769557) := by
    rw [show ((891802769557 / 250000000000) : ℝ) = ((250000000000 / 891802769557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14506_neg : (3139676133 / 1000000000) ≤ -Real.log (125000000000 / 2887048192771) ∧
    -Real.log (125000000000 / 2887048192771) ≤ (1569838069 / 500000000) := by
  have h := checkLog_sound (w := (887048192771 / 4887048192771)) (n := 12)
    (lo := (367087413 / 1000000000)) (hi := (183543707 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2887048192771 / 2000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2887048192771 / 2000000000000) = 1/(125000000000 / 2887048192771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14506 : Bounds (3139676133 / 1000000000) (1569838069 / 500000000) (Real.log (2887048192771 / 125000000000)) := by
  have h := reflection_log_14506_neg
  have he : Real.log (2887048192771 / 125000000000) = -Real.log (125000000000 / 2887048192771) := by
    rw [show ((2887048192771 / 125000000000) : ℝ) = ((125000000000 / 2887048192771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14507_neg : (794513457 / 250000000) ≤ -Real.log (1 / 24) ∧
    -Real.log (1 / 24) ≤ (3178053833 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 5)) (n := 12)
    (lo := (101366277 / 250000000)) (hi := (405465109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3 / 2) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3 / 2) = 1/(1 / 24) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14507 : Bounds (794513457 / 250000000) (3178053833 / 1000000000) (Real.log (24 / 1)) := by
  have h := reflection_log_14507_neg
  have he : Real.log (24 / 1) = -Real.log (1 / 24) := by
    rw [show ((24 / 1) : ℝ) = ((1 / 24) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14508_neg : (326943233 / 500000000) ≤ -Real.log (1000 / 1923) ∧
    -Real.log (1000 / 1923) ≤ (653886467 / 1000000000) := by
  have h := checkLog_sound (w := (923 / 2923)) (n := 12)
    (lo := (326943233 / 500000000)) (hi := (653886467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1923 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1923 / 1000) = 1/(1000 / 1923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14508 : Bounds (326943233 / 500000000) (653886467 / 1000000000) (Real.log (1923 / 1000)) := by
  have h := reflection_log_14508_neg
  have he : Real.log (1923 / 1000) = -Real.log (1000 / 1923) := by
    rw [show ((1923 / 1000) : ℝ) = ((1000 / 1923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14509_neg : (512789971 / 200000000) ≤ -Real.log (77 / 1000) ∧
    -Real.log (77 / 1000) ≤ (2563949859 / 1000000000) := by
  have h := checkLog_sound (w := (24 / 101)) (n := 12)
    (lo := (96901663 / 200000000)) (hi := (121127079 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 77) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125 / 77) = 1/(77 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14509 : Bounds (-2563949859 / 1000000000) (-512789971 / 200000000) (Real.log (77 / 1000)) := by
  have h := reflection_log_14509_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14510_neg : (461287 / 500000000) ≤ -Real.log (1000000 / 1000923) ∧
    -Real.log (1000000 / 1000923) ≤ (36903 / 40000000) := by
  have h := checkLog_sound (w := (923 / 2000923)) (n := 12)
    (lo := (461287 / 500000000)) (hi := (36903 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000923 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000923 / 1000000) = 1/(1000000 / 1000923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14510 : Bounds (461287 / 500000000) (36903 / 40000000) (Real.log (1000923 / 1000000)) := by
  have h := reflection_log_14510_neg
  have he : Real.log (1000923 / 1000000) = -Real.log (1000000 / 1000923) := by
    rw [show ((1000923 / 1000000) : ℝ) = ((1000000 / 1000923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14511_neg : (461713 / 500000000) ≤ -Real.log (999077 / 1000000) ∧
    -Real.log (999077 / 1000000) ≤ (923427 / 1000000000) := by
  have h := checkLog_sound (w := (923 / 1999077)) (n := 12)
    (lo := (461713 / 500000000)) (hi := (923427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999077) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999077) = 1/(999077 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14511 : Bounds (-923427 / 1000000000) (-461713 / 500000000) (Real.log (999077 / 1000000)) := by
  have h := reflection_log_14511_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14512_neg : (222799753 / 500000000) ≤ -Real.log (500000 / 780713) ∧
    -Real.log (500000 / 780713) ≤ (445599507 / 1000000000) := by
  have h := checkLog_sound (w := (280713 / 1280713)) (n := 12)
    (lo := (222799753 / 500000000)) (hi := (445599507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((780713 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(780713 / 500000) = 1/(500000 / 780713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14512 : Bounds (222799753 / 500000000) (445599507 / 1000000000) (Real.log (780713 / 500000)) := by
  have h := reflection_log_14512_neg
  have he : Real.log (780713 / 500000) = -Real.log (500000 / 780713) := by
    rw [show ((780713 / 500000) : ℝ) = ((500000 / 780713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14513_neg : (824226723 / 1000000000) ≤ -Real.log (219287 / 500000) ∧
    -Real.log (219287 / 500000) ≤ (32969069 / 40000000) := by
  have h := checkLog_sound (w := (30713 / 469287)) (n := 12)
    (lo := (131079543 / 1000000000)) (hi := (16384943 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 219287) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 219287) = 1/(219287 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14513 : Bounds (-32969069 / 40000000) (-824226723 / 1000000000) (Real.log (219287 / 500000)) := by
  have h := reflection_log_14513_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14514_neg : (447919689 / 1000000000) ≤ -Real.log (1000000 / 1565053) ∧
    -Real.log (1000000 / 1565053) ≤ (44791969 / 100000000) := by
  have h := checkLog_sound (w := (565053 / 2565053)) (n := 12)
    (lo := (447919689 / 1000000000)) (hi := (44791969 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1565053 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1565053 / 1000000) = 1/(1000000 / 1565053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14514 : Bounds (447919689 / 1000000000) (44791969 / 100000000) (Real.log (1565053 / 1000000)) := by
  have h := reflection_log_14514_neg
  have he : Real.log (1565053 / 1000000) = -Real.log (1000000 / 1565053) := by
    rw [show ((1565053 / 1000000) : ℝ) = ((1000000 / 1565053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14515_neg : (832531093 / 1000000000) ≤ -Real.log (434947 / 1000000) ∧
    -Real.log (434947 / 1000000) ≤ (166506219 / 200000000) := by
  have h := checkLog_sound (w := (65053 / 934947)) (n := 12)
    (lo := (139383913 / 1000000000)) (hi := (69691957 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 434947) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 434947) = 1/(434947 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14515 : Bounds (-166506219 / 200000000) (-832531093 / 1000000000) (Real.log (434947 / 1000000)) := by
  have h := reflection_log_14515_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14516_neg : (76922281 / 200000000) ≤ -Real.log (680715107191 / 1000000000000) ∧
    -Real.log (680715107191 / 1000000000000) ≤ (192305703 / 500000000) := by
  have h := checkLog_sound (w := (319284892809 / 1680715107191)) (n := 12)
    (lo := (76922281 / 200000000)) (hi := (192305703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 680715107191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 680715107191) = 1/(680715107191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14516 : Bounds (-192305703 / 500000000) (-76922281 / 200000000) (Real.log (680715107191 / 1000000000000)) := by
  have h := reflection_log_14516_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14517_neg : (378627217 / 1000000000) ≤ -Real.log (171200211631 / 250000000000) ∧
    -Real.log (171200211631 / 250000000000) ≤ (189313609 / 500000000) := by
  have h := checkLog_sound (w := (78799788369 / 421200211631)) (n := 12)
    (lo := (378627217 / 1000000000)) (hi := (189313609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 171200211631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 171200211631) = 1/(171200211631 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14517 : Bounds (-189313609 / 500000000) (-378627217 / 1000000000) (Real.log (171200211631 / 250000000000)) := by
  have h := reflection_log_14517_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14518_neg : (126982623 / 100000000) ≤ -Real.log (100000000000 / 356023384879) ∧
    -Real.log (100000000000 / 356023384879) ≤ (158728279 / 125000000) := by
  have h := checkLog_sound (w := (156023384879 / 556023384879)) (n := 12)
    (lo := (11533581 / 20000000)) (hi := (576679051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((356023384879 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(356023384879 / 200000000000) = 1/(100000000000 / 356023384879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14518 : Bounds (126982623 / 100000000) (158728279 / 125000000) (Real.log (356023384879 / 100000000000)) := by
  have h := reflection_log_14518_neg
  have he : Real.log (356023384879 / 100000000000) = -Real.log (100000000000 / 356023384879) := by
    rw [show ((356023384879 / 100000000000) : ℝ) = ((100000000000 / 356023384879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14519_neg : (1280450783 / 1000000000) ≤ -Real.log (500000000000 / 1799130698683) ∧
    -Real.log (500000000000 / 1799130698683) ≤ (256090157 / 200000000) := by
  have h := checkLog_sound (w := (799130698683 / 2799130698683)) (n := 12)
    (lo := (587303603 / 1000000000)) (hi := (146825901 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1799130698683 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1799130698683 / 1000000000000) = 1/(500000000000 / 1799130698683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14519 : Bounds (1280450783 / 1000000000) (256090157 / 200000000) (Real.log (1799130698683 / 500000000000)) := by
  have h := reflection_log_14519_neg
  have he : Real.log (1799130698683 / 500000000000) = -Real.log (500000000000 / 1799130698683) := by
    rw [show ((1799130698683 / 500000000000) : ℝ) = ((500000000000 / 1799130698683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14520_neg : (3217836321 / 1000000000) ≤ -Real.log (500000000000 / 12487012987013) ∧
    -Real.log (500000000000 / 12487012987013) ≤ (1608918163 / 500000000) := by
  have h := checkLog_sound (w := (4487012987013 / 20487012987013)) (n := 12)
    (lo := (445247601 / 1000000000)) (hi := (222623801 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12487012987013 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12487012987013 / 8000000000000) = 1/(500000000000 / 12487012987013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14520 : Bounds (3217836321 / 1000000000) (1608918163 / 500000000) (Real.log (12487012987013 / 500000000000)) := by
  have h := reflection_log_14520_neg
  have he : Real.log (12487012987013 / 500000000000) = -Real.log (500000000000 / 12487012987013) := by
    rw [show ((12487012987013 / 500000000000) : ℝ) = ((500000000000 / 12487012987013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14521_neg : (655445313 / 1000000000) ≤ -Real.log (500 / 963) ∧
    -Real.log (500 / 963) ≤ (327722657 / 500000000) := by
  have h := checkLog_sound (w := (463 / 1463)) (n := 12)
    (lo := (655445313 / 1000000000)) (hi := (327722657 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((963 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(963 / 500) = 1/(500 / 963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14521 : Bounds (655445313 / 1000000000) (327722657 / 500000000) (Real.log (963 / 500)) := by
  have h := reflection_log_14521_neg
  have he : Real.log (963 / 500) = -Real.log (500 / 963) := by
    rw [show ((963 / 500) : ℝ) = ((500 / 963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14522_neg : (325461273 / 125000000) ≤ -Real.log (37 / 500) ∧
    -Real.log (37 / 500) ≤ (650922547 / 250000000) := by
  have h := checkLog_sound (w := (51 / 199)) (n := 12)
    (lo := (131062161 / 250000000)) (hi := (104849729 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 74) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125 / 74) = 1/(37 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14522 : Bounds (-650922547 / 250000000) (-325461273 / 125000000) (Real.log (37 / 500)) := by
  have h := reflection_log_14522_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14523_neg : (925571 / 1000000000) ≤ -Real.log (500000 / 500463) ∧
    -Real.log (500000 / 500463) ≤ (231393 / 250000000) := by
  have h := checkLog_sound (w := (463 / 1000463)) (n := 12)
    (lo := (925571 / 1000000000)) (hi := (231393 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500463 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500463 / 500000) = 1/(500000 / 500463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14523 : Bounds (925571 / 1000000000) (231393 / 250000000) (Real.log (500463 / 500000)) := by
  have h := reflection_log_14523_neg
  have he : Real.log (500463 / 500000) = -Real.log (500000 / 500463) := by
    rw [show ((500463 / 500000) : ℝ) = ((500000 / 500463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14524_neg : (926429 / 1000000000) ≤ -Real.log (499537 / 500000) ∧
    -Real.log (499537 / 500000) ≤ (92643 / 100000000) := by
  have h := checkLog_sound (w := (463 / 999537)) (n := 12)
    (lo := (926429 / 1000000000)) (hi := (92643 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499537) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499537) = 1/(499537 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14524 : Bounds (-92643 / 100000000) (-926429 / 1000000000) (Real.log (499537 / 500000)) := by
  have h := reflection_log_14524_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14525_neg : (447491497 / 1000000000) ≤ -Real.log (1000000 / 1564383) ∧
    -Real.log (1000000 / 1564383) ≤ (223745749 / 500000000) := by
  have h := checkLog_sound (w := (564383 / 2564383)) (n := 12)
    (lo := (447491497 / 1000000000)) (hi := (223745749 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1564383 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1564383 / 1000000) = 1/(1000000 / 1564383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14525 : Bounds (447491497 / 1000000000) (223745749 / 500000000) (Real.log (1564383 / 1000000)) := by
  have h := reflection_log_14525_neg
  have he : Real.log (1564383 / 1000000) = -Real.log (1000000 / 1564383) := by
    rw [show ((1564383 / 1000000) : ℝ) = ((1000000 / 1564383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14526_neg : (830991861 / 1000000000) ≤ -Real.log (435617 / 1000000) ∧
    -Real.log (435617 / 1000000) ≤ (830991863 / 1000000000) := by
  have h := checkLog_sound (w := (64383 / 935617)) (n := 12)
    (lo := (137844681 / 1000000000)) (hi := (68922341 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 435617) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 435617) = 1/(435617 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14526 : Bounds (-830991863 / 1000000000) (-830991861 / 1000000000) (Real.log (435617 / 1000000)) := by
  have h := reflection_log_14526_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14527_neg : (224912259 / 500000000) ≤ -Real.log (1000000 / 1568037) ∧
    -Real.log (1000000 / 1568037) ≤ (449824519 / 1000000000) := by
  have h := checkLog_sound (w := (568037 / 2568037)) (n := 12)
    (lo := (224912259 / 500000000)) (hi := (449824519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1568037 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1568037 / 1000000) = 1/(1000000 / 1568037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14527 : Bounds (224912259 / 500000000) (449824519 / 1000000000) (Real.log (1568037 / 1000000)) := by
  have h := reflection_log_14527_neg
  have he : Real.log (1568037 / 1000000) = -Real.log (1000000 / 1568037) := by
    rw [show ((1568037 / 1000000) : ℝ) = ((1000000 / 1568037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0227 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_14528_neg : (839415341 / 1000000000) ≤ -Real.log (431963 / 1000000) ∧
    -Real.log (431963 / 1000000) ≤ (839415343 / 1000000000) := by
  have h := checkLog_sound (w := (68037 / 931963)) (n := 12)
    (lo := (146268161 / 1000000000)) (hi := (73134081 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 431963) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 431963) = 1/(431963 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14528 : Bounds (-839415343 / 1000000000) (-839415341 / 1000000000) (Real.log (431963 / 1000000)) := by
  have h := reflection_log_14528_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14529_neg : (389590823 / 1000000000) ≤ -Real.log (677333966631 / 1000000000000) ∧
    -Real.log (677333966631 / 1000000000000) ≤ (48698853 / 125000000) := by
  have h := checkLog_sound (w := (322666033369 / 1677333966631)) (n := 12)
    (lo := (389590823 / 1000000000)) (hi := (48698853 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 677333966631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 677333966631) = 1/(677333966631 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14529 : Bounds (-48698853 / 125000000) (-389590823 / 1000000000) (Real.log (677333966631 / 1000000000000)) := by
  have h := reflection_log_14529_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14530_neg : (76700073 / 200000000) ≤ -Real.log (681471829311 / 1000000000000) ∧
    -Real.log (681471829311 / 1000000000000) ≤ (191750183 / 500000000) := by
  have h := checkLog_sound (w := (318528170689 / 1681471829311)) (n := 12)
    (lo := (76700073 / 200000000)) (hi := (191750183 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 681471829311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 681471829311) = 1/(681471829311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14530 : Bounds (-191750183 / 500000000) (-76700073 / 200000000) (Real.log (681471829311 / 1000000000000)) := by
  have h := reflection_log_14530_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14531_neg : (639241679 / 500000000) ≤ -Real.log (500000000000 / 1795594524547) ∧
    -Real.log (500000000000 / 1795594524547) ≤ (7990521 / 6250000) := by
  have h := checkLog_sound (w := (795594524547 / 2795594524547)) (n := 12)
    (lo := (292668089 / 500000000)) (hi := (585336179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1795594524547 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1795594524547 / 1000000000000) = 1/(500000000000 / 1795594524547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14531 : Bounds (639241679 / 500000000) (7990521 / 6250000) (Real.log (1795594524547 / 500000000000)) := by
  have h := reflection_log_14531_neg
  have he : Real.log (1795594524547 / 500000000000) = -Real.log (500000000000 / 1795594524547) := by
    rw [show ((1795594524547 / 500000000000) : ℝ) = ((500000000000 / 1795594524547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14532_neg : (64461993 / 50000000) ≤ -Real.log (2500000000 / 9075065457) ∧
    -Real.log (2500000000 / 9075065457) ≤ (644619931 / 500000000) := by
  have h := checkLog_sound (w := (4075065457 / 14075065457)) (n := 12)
    (lo := (14902317 / 25000000)) (hi := (596092681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9075065457 / 5000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(9075065457 / 5000000000) = 1/(2500000000 / 9075065457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14532 : Bounds (64461993 / 50000000) (644619931 / 500000000) (Real.log (9075065457 / 2500000000)) := by
  have h := reflection_log_14532_neg
  have he : Real.log (9075065457 / 2500000000) = -Real.log (2500000000 / 9075065457) := by
    rw [show ((9075065457 / 2500000000) : ℝ) = ((2500000000 / 9075065457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14533_neg : (3217836321 / 1000000000) ≤ -Real.log (125000000000 / 3121753246753) ∧
    -Real.log (125000000000 / 3121753246753) ≤ (1608918163 / 500000000) := by
  have h := checkLog_sound (w := (1121753246753 / 5121753246753)) (n := 12)
    (lo := (445247601 / 1000000000)) (hi := (222623801 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3121753246753 / 2000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3121753246753 / 2000000000000) = 1/(125000000000 / 3121753246753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14533 : Bounds (3217836321 / 1000000000) (1608918163 / 500000000) (Real.log (3121753246753 / 125000000000)) := by
  have h := reflection_log_14533_neg
  have he : Real.log (3121753246753 / 125000000000) = -Real.log (125000000000 / 3121753246753) := by
    rw [show ((3121753246753 / 125000000000) : ℝ) = ((125000000000 / 3121753246753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14534_neg : (407391937 / 125000000) ≤ -Real.log (250000000000 / 6506756756757) ∧
    -Real.log (250000000000 / 6506756756757) ≤ (3259135501 / 1000000000) := by
  have h := checkLog_sound (w := (2506756756757 / 10506756756757)) (n := 12)
    (lo := (60818347 / 125000000)) (hi := (486546777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6506756756757 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6506756756757 / 4000000000000) = 1/(250000000000 / 6506756756757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14534 : Bounds (407391937 / 125000000) (3259135501 / 1000000000) (Real.log (6506756756757 / 250000000000)) := by
  have h := reflection_log_14534_neg
  have he : Real.log (6506756756757 / 250000000000) = -Real.log (250000000000 / 6506756756757) := by
    rw [show ((6506756756757 / 250000000000) : ℝ) = ((250000000000 / 6506756756757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14535_neg : (657001733 / 1000000000) ≤ -Real.log (1000 / 1929) ∧
    -Real.log (1000 / 1929) ≤ (328500867 / 500000000) := by
  have h := checkLog_sound (w := (929 / 2929)) (n := 12)
    (lo := (657001733 / 1000000000)) (hi := (328500867 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1929 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1929 / 1000) = 1/(1000 / 1929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14535 : Bounds (657001733 / 1000000000) (328500867 / 500000000) (Real.log (1929 / 1000)) := by
  have h := reflection_log_14535_neg
  have he : Real.log (1929 / 1000) = -Real.log (1000 / 1929) := by
    rw [show ((1929 / 1000) : ℝ) = ((1000 / 1929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14536_neg : (13225377 / 5000000) ≤ -Real.log (71 / 1000) ∧
    -Real.log (71 / 1000) ≤ (661268851 / 250000000) := by
  have h := checkLog_sound (w := (27 / 98)) (n := 12)
    (lo := (28281693 / 50000000)) (hi := (565633861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 71) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125 / 71) = 1/(71 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14536 : Bounds (-661268851 / 250000000) (-13225377 / 5000000) (Real.log (71 / 1000)) := by
  have h := reflection_log_14536_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14537_neg : (116071 / 125000000) ≤ -Real.log (1000000 / 1000929) ∧
    -Real.log (1000000 / 1000929) ≤ (928569 / 1000000000) := by
  have h := checkLog_sound (w := (929 / 2000929)) (n := 12)
    (lo := (116071 / 125000000)) (hi := (928569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000929 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000929 / 1000000) = 1/(1000000 / 1000929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14537 : Bounds (116071 / 125000000) (928569 / 1000000000) (Real.log (1000929 / 1000000)) := by
  have h := reflection_log_14537_neg
  have he : Real.log (1000929 / 1000000) = -Real.log (1000000 / 1000929) := by
    rw [show ((1000929 / 1000000) : ℝ) = ((1000000 / 1000929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14538_neg : (929431 / 1000000000) ≤ -Real.log (999071 / 1000000) ∧
    -Real.log (999071 / 1000000) ≤ (116179 / 125000000) := by
  have h := checkLog_sound (w := (929 / 1999071)) (n := 12)
    (lo := (929431 / 1000000000)) (hi := (116179 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999071) = 1/(999071 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14538 : Bounds (-116179 / 125000000) (-929431 / 1000000000) (Real.log (999071 / 1000000)) := by
  have h := reflection_log_14538_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14539_neg : (449397779 / 1000000000) ≤ -Real.log (125000 / 195921) ∧
    -Real.log (125000 / 195921) ≤ (22469889 / 50000000) := by
  have h := checkLog_sound (w := (70921 / 320921)) (n := 12)
    (lo := (449397779 / 1000000000)) (hi := (22469889 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((195921 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(195921 / 125000) = 1/(125000 / 195921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14539 : Bounds (449397779 / 1000000000) (22469889 / 50000000) (Real.log (195921 / 125000)) := by
  have h := reflection_log_14539_neg
  have he : Real.log (195921 / 125000) = -Real.log (125000 / 195921) := by
    rw [show ((195921 / 125000) : ℝ) = ((125000 / 195921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14540_neg : (209466949 / 250000000) ≤ -Real.log (54079 / 125000) ∧
    -Real.log (54079 / 125000) ≤ (418933899 / 500000000) := by
  have h := checkLog_sound (w := (8421 / 116579)) (n := 12)
    (lo := (18090077 / 125000000)) (hi := (144720617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 54079) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 54079) = 1/(54079 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14540 : Bounds (-418933899 / 500000000) (-209466949 / 250000000) (Real.log (54079 / 125000)) := by
  have h := reflection_log_14540_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14541_neg : (451743549 / 1000000000) ≤ -Real.log (1000000 / 1571049) ∧
    -Real.log (1000000 / 1571049) ≤ (9034871 / 20000000) := by
  have h := checkLog_sound (w := (571049 / 2571049)) (n := 12)
    (lo := (451743549 / 1000000000)) (hi := (9034871 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1571049 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1571049 / 1000000) = 1/(1000000 / 1571049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14541 : Bounds (451743549 / 1000000000) (9034871 / 20000000) (Real.log (1571049 / 1000000)) := by
  have h := reflection_log_14541_neg
  have he : Real.log (1571049 / 1000000) = -Real.log (1000000 / 1571049) := by
    rw [show ((1571049 / 1000000) : ℝ) = ((1000000 / 1571049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14542_neg : (169282517 / 200000000) ≤ -Real.log (428951 / 1000000) ∧
    -Real.log (428951 / 1000000) ≤ (846412587 / 1000000000) := by
  have h := checkLog_sound (w := (71049 / 928951)) (n := 12)
    (lo := (30653081 / 200000000)) (hi := (76632703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 428951) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 428951) = 1/(428951 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14542 : Bounds (-846412587 / 1000000000) (-169282517 / 200000000) (Real.log (428951 / 1000000)) := by
  have h := reflection_log_14542_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14543_neg : (98667259 / 250000000) ≤ -Real.log (673903039599 / 1000000000000) ∧
    -Real.log (673903039599 / 1000000000000) ≤ (394669037 / 1000000000) := by
  have h := checkLog_sound (w := (326096960401 / 1673903039599)) (n := 12)
    (lo := (98667259 / 250000000)) (hi := (394669037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 673903039599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 673903039599) = 1/(673903039599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14543 : Bounds (-394669037 / 1000000000) (-98667259 / 250000000) (Real.log (673903039599 / 1000000000000)) := by
  have h := reflection_log_14543_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14544_neg : (388470017 / 1000000000) ≤ -Real.log (10595211759 / 15625000000) ∧
    -Real.log (10595211759 / 15625000000) ≤ (194235009 / 500000000) := by
  have h := checkLog_sound (w := (5029788241 / 26220211759)) (n := 12)
    (lo := (388470017 / 1000000000)) (hi := (194235009 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 10595211759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 10595211759) = 1/(10595211759 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14544 : Bounds (-194235009 / 500000000) (-388470017 / 1000000000) (Real.log (10595211759 / 15625000000)) := by
  have h := reflection_log_14544_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14545_neg : (51490623 / 40000000) ≤ -Real.log (62500000000 / 226429159193) ∧
    -Real.log (62500000000 / 226429159193) ≤ (1287265577 / 1000000000) := by
  have h := checkLog_sound (w := (101429159193 / 351429159193)) (n := 12)
    (lo := (118823679 / 200000000)) (hi := (148529599 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((226429159193 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(226429159193 / 125000000000) = 1/(62500000000 / 226429159193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14545 : Bounds (51490623 / 40000000) (1287265577 / 1000000000) (Real.log (226429159193 / 62500000000)) := by
  have h := reflection_log_14545_neg
  have he : Real.log (226429159193 / 62500000000) = -Real.log (62500000000 / 226429159193) := by
    rw [show ((226429159193 / 62500000000) : ℝ) = ((62500000000 / 226429159193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14546_neg : (649078067 / 500000000) ≤ -Real.log (250000000000 / 915634303219) ∧
    -Real.log (250000000000 / 915634303219) ≤ (162269517 / 125000000) := by
  have h := checkLog_sound (w := (415634303219 / 1415634303219)) (n := 12)
    (lo := (302504477 / 500000000)) (hi := (121001791 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((915634303219 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(915634303219 / 500000000000) = 1/(250000000000 / 915634303219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14546 : Bounds (649078067 / 500000000) (162269517 / 125000000) (Real.log (915634303219 / 250000000000)) := by
  have h := reflection_log_14546_neg
  have he : Real.log (915634303219 / 250000000000) = -Real.log (250000000000 / 915634303219) := by
    rw [show ((915634303219 / 250000000000) : ℝ) = ((250000000000 / 915634303219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14547_neg : (407391937 / 125000000) ≤ -Real.log (500000000000 / 13013513513513) ∧
    -Real.log (500000000000 / 13013513513513) ≤ (3259135501 / 1000000000) := by
  have h := checkLog_sound (w := (5013513513513 / 21013513513513)) (n := 12)
    (lo := (60818347 / 125000000)) (hi := (486546777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13013513513513 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(13013513513513 / 8000000000000) = 1/(500000000000 / 13013513513513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14547 : Bounds (407391937 / 125000000) (3259135501 / 1000000000) (Real.log (13013513513513 / 500000000000)) := by
  have h := reflection_log_14547_neg
  have he : Real.log (13013513513513 / 500000000000) = -Real.log (500000000000 / 13013513513513) := by
    rw [show ((13013513513513 / 500000000000) : ℝ) = ((500000000000 / 13013513513513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14548_neg : (3302077133 / 1000000000) ≤ -Real.log (250000000000 / 6792253521127) ∧
    -Real.log (250000000000 / 6792253521127) ≤ (1651038569 / 500000000) := by
  have h := checkLog_sound (w := (2792253521127 / 10792253521127)) (n := 12)
    (lo := (529488413 / 1000000000)) (hi := (264744207 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6792253521127 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6792253521127 / 4000000000000) = 1/(250000000000 / 6792253521127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14548 : Bounds (3302077133 / 1000000000) (1651038569 / 500000000) (Real.log (6792253521127 / 250000000000)) := by
  have h := reflection_log_14548_neg
  have he : Real.log (6792253521127 / 250000000000) = -Real.log (250000000000 / 6792253521127) := by
    rw [show ((6792253521127 / 250000000000) : ℝ) = ((250000000000 / 6792253521127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14549_neg : (131711147 / 200000000) ≤ -Real.log (250 / 483) ∧
    -Real.log (250 / 483) ≤ (82319467 / 125000000) := by
  have h := checkLog_sound (w := (233 / 733)) (n := 12)
    (lo := (131711147 / 200000000)) (hi := (82319467 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((483 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(483 / 250) = 1/(250 / 483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14549 : Bounds (131711147 / 200000000) (82319467 / 125000000) (Real.log (483 / 250)) := by
  have h := reflection_log_14549_neg
  have he : Real.log (483 / 250) = -Real.log (250 / 483) := by
    rw [show ((483 / 250) : ℝ) = ((250 / 483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14550_neg : (672061893 / 250000000) ≤ -Real.log (17 / 250) ∧
    -Real.log (17 / 250) ≤ (336030947 / 125000000) := by
  have h := checkLog_sound (w := (57 / 193)) (n := 12)
    (lo := (38050377 / 62500000)) (hi := (608806033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 68) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125 / 68) = 1/(17 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14550 : Bounds (-336030947 / 125000000) (-672061893 / 250000000) (Real.log (17 / 250)) := by
  have h := reflection_log_14550_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14551_neg : (186313 / 200000000) ≤ -Real.log (250000 / 250233) ∧
    -Real.log (250000 / 250233) ≤ (465783 / 500000000) := by
  have h := checkLog_sound (w := (233 / 500233)) (n := 12)
    (lo := (186313 / 200000000)) (hi := (465783 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250233 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250233 / 250000) = 1/(250000 / 250233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14551 : Bounds (186313 / 200000000) (465783 / 500000000) (Real.log (250233 / 250000)) := by
  have h := reflection_log_14551_neg
  have he : Real.log (250233 / 250000) = -Real.log (250000 / 250233) := by
    rw [show ((250233 / 250000) : ℝ) = ((250000 / 250233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14552_neg : (466217 / 500000000) ≤ -Real.log (249767 / 250000) ∧
    -Real.log (249767 / 250000) ≤ (186487 / 200000000) := by
  have h := checkLog_sound (w := (233 / 499767)) (n := 12)
    (lo := (466217 / 500000000)) (hi := (186487 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249767) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249767) = 1/(249767 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14552 : Bounds (-186487 / 200000000) (-466217 / 500000000) (Real.log (249767 / 250000)) := by
  have h := reflection_log_14552_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14553_neg : (90263653 / 200000000) ≤ -Real.log (1000000 / 1570381) ∧
    -Real.log (1000000 / 1570381) ≤ (225659133 / 500000000) := by
  have h := checkLog_sound (w := (570381 / 2570381)) (n := 12)
    (lo := (90263653 / 200000000)) (hi := (225659133 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1570381 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1570381 / 1000000) = 1/(1000000 / 1570381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14553 : Bounds (90263653 / 200000000) (225659133 / 500000000) (Real.log (1570381 / 1000000)) := by
  have h := reflection_log_14553_neg
  have he : Real.log (1570381 / 1000000) = -Real.log (1000000 / 1570381) := by
    rw [show ((1570381 / 1000000) : ℝ) = ((1000000 / 1570381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14554_neg : (844856509 / 1000000000) ≤ -Real.log (429619 / 1000000) ∧
    -Real.log (429619 / 1000000) ≤ (844856511 / 1000000000) := by
  have h := checkLog_sound (w := (70381 / 929619)) (n := 12)
    (lo := (151709329 / 1000000000)) (hi := (15170933 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 429619) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 429619) = 1/(429619 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14554 : Bounds (-844856511 / 1000000000) (-844856509 / 1000000000) (Real.log (429619 / 1000000)) := by
  have h := reflection_log_14554_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14555_neg : (226838981 / 500000000) ≤ -Real.log (1000000 / 1574091) ∧
    -Real.log (1000000 / 1574091) ≤ (453677963 / 1000000000) := by
  have h := checkLog_sound (w := (574091 / 2574091)) (n := 12)
    (lo := (226838981 / 500000000)) (hi := (453677963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1574091 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1574091 / 1000000) = 1/(1000000 / 1574091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14555 : Bounds (226838981 / 500000000) (453677963 / 1000000000) (Real.log (1574091 / 1000000)) := by
  have h := reflection_log_14555_neg
  have he : Real.log (1574091 / 1000000) = -Real.log (1000000 / 1574091) := by
    rw [show ((1574091 / 1000000) : ℝ) = ((1000000 / 1574091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14556_neg : (853529569 / 1000000000) ≤ -Real.log (425909 / 1000000) ∧
    -Real.log (425909 / 1000000) ≤ (853529571 / 1000000000) := by
  have h := checkLog_sound (w := (74091 / 925909)) (n := 12)
    (lo := (160382389 / 1000000000)) (hi := (16038239 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 425909) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 425909) = 1/(425909 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14556 : Bounds (-853529571 / 1000000000) (-853529569 / 1000000000) (Real.log (425909 / 1000000)) := by
  have h := reflection_log_14556_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14557_neg : (399851607 / 1000000000) ≤ -Real.log (670419523719 / 1000000000000) ∧
    -Real.log (670419523719 / 1000000000000) ≤ (49981451 / 125000000) := by
  have h := checkLog_sound (w := (329580476281 / 1670419523719)) (n := 12)
    (lo := (399851607 / 1000000000)) (hi := (49981451 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 670419523719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 670419523719) = 1/(670419523719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14557 : Bounds (-49981451 / 125000000) (-399851607 / 1000000000) (Real.log (670419523719 / 1000000000000)) := by
  have h := reflection_log_14557_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14558_neg : (98384561 / 250000000) ≤ -Real.log (674665514839 / 1000000000000) ∧
    -Real.log (674665514839 / 1000000000000) ≤ (78707649 / 200000000) := by
  have h := checkLog_sound (w := (325334485161 / 1674665514839)) (n := 12)
    (lo := (98384561 / 250000000)) (hi := (78707649 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 674665514839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 674665514839) = 1/(674665514839 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14558 : Bounds (-78707649 / 200000000) (-98384561 / 250000000) (Real.log (674665514839 / 1000000000000)) := by
  have h := reflection_log_14558_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14559_neg : (648087387 / 500000000) ≤ -Real.log (250000000000 / 913821898007) ∧
    -Real.log (250000000000 / 913821898007) ≤ (162021847 / 125000000) := by
  have h := checkLog_sound (w := (413821898007 / 1413821898007)) (n := 12)
    (lo := (301513797 / 500000000)) (hi := (120605519 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((913821898007 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(913821898007 / 500000000000) = 1/(250000000000 / 913821898007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14559 : Bounds (648087387 / 500000000) (162021847 / 125000000) (Real.log (913821898007 / 250000000000)) := by
  have h := reflection_log_14559_neg
  have he : Real.log (913821898007 / 250000000000) = -Real.log (250000000000 / 913821898007) := by
    rw [show ((913821898007 / 250000000000) : ℝ) = ((250000000000 / 913821898007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14560_neg : (326801883 / 250000000) ≤ -Real.log (976562500 / 3609217561) ∧
    -Real.log (976562500 / 3609217561) ≤ (653603767 / 500000000) := by
  have h := checkLog_sound (w := (1656092561 / 5562342561)) (n := 12)
    (lo := (9594693 / 15625000)) (hi := (614060353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3609217561 / 1953125000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(3609217561 / 1953125000) = 1/(976562500 / 3609217561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14560 : Bounds (326801883 / 250000000) (653603767 / 500000000) (Real.log (3609217561 / 976562500)) := by
  have h := reflection_log_14560_neg
  have he : Real.log (3609217561 / 976562500) = -Real.log (976562500 / 3609217561) := by
    rw [show ((3609217561 / 976562500) : ℝ) = ((976562500 / 3609217561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14561_neg : (3302077133 / 1000000000) ≤ -Real.log (500000000000 / 13584507042253) ∧
    -Real.log (500000000000 / 13584507042253) ≤ (1651038569 / 500000000) := by
  have h := checkLog_sound (w := (5584507042253 / 21584507042253)) (n := 12)
    (lo := (529488413 / 1000000000)) (hi := (264744207 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13584507042253 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(13584507042253 / 8000000000000) = 1/(500000000000 / 13584507042253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14561 : Bounds (3302077133 / 1000000000) (1651038569 / 500000000) (Real.log (13584507042253 / 500000000000)) := by
  have h := reflection_log_14561_neg
  have he : Real.log (13584507042253 / 500000000000) = -Real.log (500000000000 / 13584507042253) := by
    rw [show ((13584507042253 / 500000000000) : ℝ) = ((500000000000 / 13584507042253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14562_neg : (3346803307 / 1000000000) ≤ -Real.log (250000000000 / 7102941176471) ∧
    -Real.log (250000000000 / 7102941176471) ≤ (209175207 / 62500000) := by
  have h := checkLog_sound (w := (3102941176471 / 11102941176471)) (n := 12)
    (lo := (574214587 / 1000000000)) (hi := (143553647 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7102941176471 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(7102941176471 / 4000000000000) = 1/(250000000000 / 7102941176471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14562 : Bounds (3346803307 / 1000000000) (209175207 / 62500000) (Real.log (7102941176471 / 250000000000)) := by
  have h := reflection_log_14562_neg
  have he : Real.log (7102941176471 / 250000000000) = -Real.log (250000000000 / 7102941176471) := by
    rw [show ((7102941176471 / 250000000000) : ℝ) = ((250000000000 / 7102941176471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14563_neg : (330053663 / 500000000) ≤ -Real.log (200 / 387) ∧
    -Real.log (200 / 387) ≤ (660107327 / 1000000000) := by
  have h := checkLog_sound (w := (187 / 587)) (n := 12)
    (lo := (330053663 / 500000000)) (hi := (660107327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((387 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(387 / 200) = 1/(200 / 387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14563 : Bounds (330053663 / 500000000) (660107327 / 1000000000) (Real.log (387 / 200)) := by
  have h := reflection_log_14563_neg
  have he : Real.log (387 / 200) = -Real.log (200 / 387) := by
    rw [show ((387 / 200) : ℝ) = ((200 / 387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14564_neg : (2733368007 / 1000000000) ≤ -Real.log (13 / 200) ∧
    -Real.log (13 / 200) ≤ (2733368011 / 1000000000) := by
  have h := checkLog_sound (w := (6 / 19)) (n := 12)
    (lo := (653926467 / 1000000000)) (hi := (163481617 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 13) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(25 / 13) = 1/(13 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14564 : Bounds (-2733368011 / 1000000000) (-2733368007 / 1000000000) (Real.log (13 / 200)) := by
  have h := reflection_log_14564_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14565_neg : (934563 / 1000000000) ≤ -Real.log (200000 / 200187) ∧
    -Real.log (200000 / 200187) ≤ (233641 / 250000000) := by
  have h := checkLog_sound (w := (187 / 400187)) (n := 12)
    (lo := (934563 / 1000000000)) (hi := (233641 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200187 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200187 / 200000) = 1/(200000 / 200187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14565 : Bounds (934563 / 1000000000) (233641 / 250000000) (Real.log (200187 / 200000)) := by
  have h := reflection_log_14565_neg
  have he : Real.log (200187 / 200000) = -Real.log (200000 / 200187) := by
    rw [show ((200187 / 200000) : ℝ) = ((200000 / 200187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14566_neg : (935437 / 1000000000) ≤ -Real.log (199813 / 200000) ∧
    -Real.log (199813 / 200000) ≤ (467719 / 500000000) := by
  have h := checkLog_sound (w := (187 / 399813)) (n := 12)
    (lo := (935437 / 1000000000)) (hi := (467719 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199813) = 1/(199813 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14566 : Bounds (-467719 / 500000000) (-935437 / 1000000000) (Real.log (199813 / 200000)) := by
  have h := reflection_log_14566_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14567_neg : (56656767 / 125000000) ≤ -Real.log (62500 / 98339) ∧
    -Real.log (62500 / 98339) ≤ (453254137 / 1000000000) := by
  have h := checkLog_sound (w := (35839 / 160839)) (n := 12)
    (lo := (56656767 / 125000000)) (hi := (453254137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98339 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98339 / 62500) = 1/(62500 / 98339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14567 : Bounds (56656767 / 125000000) (453254137 / 1000000000) (Real.log (98339 / 62500)) := by
  have h := reflection_log_14567_neg
  have he : Real.log (98339 / 62500) = -Real.log (62500 / 98339) := by
    rw [show ((98339 / 62500) : ℝ) = ((62500 / 98339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14568_neg : (212991183 / 250000000) ≤ -Real.log (26661 / 62500) ∧
    -Real.log (26661 / 62500) ≤ (425982367 / 500000000) := by
  have h := checkLog_sound (w := (4589 / 57911)) (n := 12)
    (lo := (9926097 / 62500000)) (hi := (158817553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 26661) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31250 / 26661) = 1/(26661 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14568 : Bounds (-425982367 / 500000000) (-212991183 / 250000000) (Real.log (26661 / 62500)) := by
  have h := reflection_log_14568_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14569_neg : (455628297 / 1000000000) ≤ -Real.log (250000 / 394291) ∧
    -Real.log (250000 / 394291) ≤ (227814149 / 500000000) := by
  have h := checkLog_sound (w := (144291 / 644291)) (n := 12)
    (lo := (455628297 / 1000000000)) (hi := (227814149 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((394291 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(394291 / 250000) = 1/(250000 / 394291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14569 : Bounds (455628297 / 1000000000) (227814149 / 500000000) (Real.log (394291 / 250000)) := by
  have h := reflection_log_14569_neg
  have he : Real.log (394291 / 250000) = -Real.log (250000 / 394291) := by
    rw [show ((394291 / 250000) : ℝ) = ((250000 / 394291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14570_neg : (860770881 / 1000000000) ≤ -Real.log (105709 / 250000) ∧
    -Real.log (105709 / 250000) ≤ (860770883 / 1000000000) := by
  have h := checkLog_sound (w := (19291 / 230709)) (n := 12)
    (lo := (167623701 / 1000000000)) (hi := (83811851 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 105709) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 105709) = 1/(105709 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14570 : Bounds (-860770883 / 1000000000) (-860770881 / 1000000000) (Real.log (105709 / 250000)) := by
  have h := reflection_log_14570_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14571_neg : (50642823 / 125000000) ≤ -Real.log (41680107319 / 62500000000) ∧
    -Real.log (41680107319 / 62500000000) ≤ (81028517 / 200000000) := by
  have h := checkLog_sound (w := (20819892681 / 104180107319)) (n := 12)
    (lo := (50642823 / 125000000)) (hi := (81028517 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 41680107319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 41680107319) = 1/(41680107319 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14571 : Bounds (-81028517 / 200000000) (-50642823 / 125000000) (Real.log (41680107319 / 62500000000)) := by
  have h := reflection_log_14571_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14572_neg : (99677649 / 250000000) ≤ -Real.log (2621816079 / 3906250000) ∧
    -Real.log (2621816079 / 3906250000) ≤ (398710597 / 1000000000) := by
  have h := checkLog_sound (w := (1284433921 / 6528066079)) (n := 12)
    (lo := (99677649 / 250000000)) (hi := (398710597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 2621816079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 2621816079) = 1/(2621816079 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14572 : Bounds (-398710597 / 1000000000) (-99677649 / 250000000) (Real.log (2621816079 / 3906250000)) := by
  have h := reflection_log_14572_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14573_neg : (1305218869 / 1000000000) ≤ -Real.log (125000000000 / 461062038183) ∧
    -Real.log (125000000000 / 461062038183) ≤ (1305218871 / 1000000000) := by
  have h := checkLog_sound (w := (211062038183 / 711062038183)) (n := 12)
    (lo := (612071689 / 1000000000)) (hi := (61207169 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((461062038183 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(461062038183 / 250000000000) = 1/(125000000000 / 461062038183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14573 : Bounds (1305218869 / 1000000000) (1305218871 / 1000000000) (Real.log (461062038183 / 125000000000)) := by
  have h := reflection_log_14573_neg
  have he : Real.log (461062038183 / 125000000000) = -Real.log (125000000000 / 461062038183) := by
    rw [show ((461062038183 / 125000000000) : ℝ) = ((125000000000 / 461062038183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14574_neg : (658199589 / 500000000) ≤ -Real.log (500000000000 / 1864983114021) ∧
    -Real.log (500000000000 / 1864983114021) ≤ (65819959 / 50000000) := by
  have h := checkLog_sound (w := (864983114021 / 2864983114021)) (n := 12)
    (lo := (311625999 / 500000000)) (hi := (623251999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1864983114021 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1864983114021 / 1000000000000) = 1/(500000000000 / 1864983114021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14574 : Bounds (658199589 / 500000000) (65819959 / 50000000) (Real.log (1864983114021 / 500000000000)) := by
  have h := reflection_log_14574_neg
  have he : Real.log (1864983114021 / 500000000000) = -Real.log (500000000000 / 1864983114021) := by
    rw [show ((1864983114021 / 500000000000) : ℝ) = ((500000000000 / 1864983114021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14575_neg : (3346803307 / 1000000000) ≤ -Real.log (500000000000 / 14205882352941) ∧
    -Real.log (500000000000 / 14205882352941) ≤ (209175207 / 62500000) := by
  have h := checkLog_sound (w := (6205882352941 / 22205882352941)) (n := 12)
    (lo := (574214587 / 1000000000)) (hi := (143553647 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14205882352941 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(14205882352941 / 8000000000000) = 1/(500000000000 / 14205882352941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14575 : Bounds (3346803307 / 1000000000) (209175207 / 62500000) (Real.log (14205882352941 / 500000000000)) := by
  have h := reflection_log_14575_neg
  have he : Real.log (14205882352941 / 500000000000) = -Real.log (500000000000 / 14205882352941) := by
    rw [show ((14205882352941 / 500000000000) : ℝ) = ((500000000000 / 14205882352941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14576_neg : (3393475333 / 1000000000) ≤ -Real.log (62500000000 / 1860576923077) ∧
    -Real.log (62500000000 / 1860576923077) ≤ (1696737669 / 500000000) := by
  have h := checkLog_sound (w := (860576923077 / 2860576923077)) (n := 12)
    (lo := (620886613 / 1000000000)) (hi := (310443307 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1860576923077 / 1000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1860576923077 / 1000000000000) = 1/(62500000000 / 1860576923077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14576 : Bounds (3393475333 / 1000000000) (1696737669 / 500000000) (Real.log (1860576923077 / 62500000000)) := by
  have h := reflection_log_14576_neg
  have he : Real.log (1860576923077 / 62500000000) = -Real.log (62500000000 / 1860576923077) := by
    rw [show ((1860576923077 / 62500000000) : ℝ) = ((62500000000 / 1860576923077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14577_neg : (661656513 / 1000000000) ≤ -Real.log (500 / 969) ∧
    -Real.log (500 / 969) ≤ (330828257 / 500000000) := by
  have h := checkLog_sound (w := (469 / 1469)) (n := 12)
    (lo := (661656513 / 1000000000)) (hi := (330828257 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((969 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(969 / 500) = 1/(500 / 969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14577 : Bounds (661656513 / 1000000000) (330828257 / 500000000) (Real.log (969 / 500)) := by
  have h := reflection_log_14577_neg
  have he : Real.log (969 / 500) = -Real.log (500 / 969) := by
    rw [show ((969 / 500) : ℝ) = ((500 / 969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14578_neg : (2780620891 / 1000000000) ≤ -Real.log (31 / 500) ∧
    -Real.log (31 / 500) ≤ (86894403 / 31250000) := by
  have h := checkLog_sound (w := (1 / 249)) (n := 12)
    (lo := (8032171 / 1000000000)) (hi := (2008043 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 124) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(125 / 124) = 1/(31 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14578 : Bounds (-86894403 / 31250000) (-2780620891 / 1000000000) (Real.log (31 / 500)) := by
  have h := reflection_log_14578_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14579_neg : (23439 / 25000000) ≤ -Real.log (500000 / 500469) ∧
    -Real.log (500000 / 500469) ≤ (937561 / 1000000000) := by
  have h := checkLog_sound (w := (469 / 1000469)) (n := 12)
    (lo := (23439 / 25000000)) (hi := (937561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500469 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500469 / 500000) = 1/(500000 / 500469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14579 : Bounds (23439 / 25000000) (937561 / 1000000000) (Real.log (500469 / 500000)) := by
  have h := reflection_log_14579_neg
  have he : Real.log (500469 / 500000) = -Real.log (500000 / 500469) := by
    rw [show ((500469 / 500000) : ℝ) = ((500000 / 500469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14580_neg : (23461 / 25000000) ≤ -Real.log (499531 / 500000) ∧
    -Real.log (499531 / 500000) ≤ (938441 / 1000000000) := by
  have h := checkLog_sound (w := (469 / 999531)) (n := 12)
    (lo := (23461 / 25000000)) (hi := (938441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499531) = 1/(499531 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14580 : Bounds (-938441 / 1000000000) (-23461 / 25000000) (Real.log (499531 / 500000)) := by
  have h := reflection_log_14580_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14581_neg : (455205931 / 1000000000) ≤ -Real.log (500000 / 788249) ∧
    -Real.log (500000 / 788249) ≤ (113801483 / 250000000) := by
  have h := checkLog_sound (w := (288249 / 1288249)) (n := 12)
    (lo := (455205931 / 1000000000)) (hi := (113801483 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((788249 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(788249 / 500000) = 1/(500000 / 788249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14581 : Bounds (455205931 / 1000000000) (113801483 / 250000000) (Real.log (788249 / 500000)) := by
  have h := reflection_log_14581_neg
  have he : Real.log (788249 / 500000) = -Real.log (500000 / 788249) := by
    rw [show ((788249 / 500000) : ℝ) = ((500000 / 788249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14582_neg : (859197041 / 1000000000) ≤ -Real.log (211751 / 500000) ∧
    -Real.log (211751 / 500000) ≤ (859197043 / 1000000000) := by
  have h := checkLog_sound (w := (38249 / 461751)) (n := 12)
    (lo := (166049861 / 1000000000)) (hi := (83024931 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 211751) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 211751) = 1/(211751 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14582 : Bounds (-859197043 / 1000000000) (-859197041 / 1000000000) (Real.log (211751 / 500000)) := by
  have h := reflection_log_14582_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14583_neg : (228797859 / 500000000) ≤ -Real.log (100000 / 158027) ∧
    -Real.log (100000 / 158027) ≤ (457595719 / 1000000000) := by
  have h := checkLog_sound (w := (58027 / 258027)) (n := 12)
    (lo := (228797859 / 500000000)) (hi := (457595719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((158027 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(158027 / 100000) = 1/(100000 / 158027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14583 : Bounds (228797859 / 500000000) (457595719 / 1000000000) (Real.log (158027 / 100000)) := by
  have h := reflection_log_14583_neg
  have he : Real.log (158027 / 100000) = -Real.log (100000 / 158027) := by
    rw [show ((158027 / 100000) : ℝ) = ((100000 / 158027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14584_neg : (868143631 / 1000000000) ≤ -Real.log (41973 / 100000) ∧
    -Real.log (41973 / 100000) ≤ (868143633 / 1000000000) := by
  have h := checkLog_sound (w := (8027 / 91973)) (n := 12)
    (lo := (174996451 / 1000000000)) (hi := (43749113 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 41973) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 41973) = 1/(41973 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14584 : Bounds (-868143633 / 1000000000) (-868143631 / 1000000000) (Real.log (41973 / 100000)) := by
  have h := reflection_log_14584_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14585_neg : (410547913 / 1000000000) ≤ -Real.log (6632867271 / 10000000000) ∧
    -Real.log (6632867271 / 10000000000) ≤ (205273957 / 500000000) := by
  have h := checkLog_sound (w := (3367132729 / 16632867271)) (n := 12)
    (lo := (410547913 / 1000000000)) (hi := (205273957 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 6632867271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 6632867271) = 1/(6632867271 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14585 : Bounds (-205273957 / 500000000) (-410547913 / 1000000000) (Real.log (6632867271 / 10000000000)) := by
  have h := reflection_log_14585_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14586_neg : (40399111 / 100000000) ≤ -Real.log (166912513999 / 250000000000) ∧
    -Real.log (166912513999 / 250000000000) ≤ (403991111 / 1000000000) := by
  have h := checkLog_sound (w := (83087486001 / 416912513999)) (n := 12)
    (lo := (40399111 / 100000000)) (hi := (403991111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 166912513999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 166912513999) = 1/(166912513999 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14586 : Bounds (-403991111 / 1000000000) (-40399111 / 100000000) (Real.log (166912513999 / 250000000000)) := by
  have h := reflection_log_14586_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14587_neg : (1314402973 / 1000000000) ≤ -Real.log (6250000000 / 23265799217) ∧
    -Real.log (6250000000 / 23265799217) ≤ (52576119 / 40000000) := by
  have h := checkLog_sound (w := (10765799217 / 35765799217)) (n := 12)
    (lo := (621255793 / 1000000000)) (hi := (310627897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23265799217 / 12500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(23265799217 / 12500000000) = 1/(6250000000 / 23265799217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14587 : Bounds (1314402973 / 1000000000) (52576119 / 40000000) (Real.log (23265799217 / 6250000000)) := by
  have h := reflection_log_14587_neg
  have he : Real.log (23265799217 / 6250000000) = -Real.log (6250000000 / 23265799217) := by
    rw [show ((23265799217 / 6250000000) : ℝ) = ((6250000000 / 23265799217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14588_neg : (1325739349 / 1000000000) ≤ -Real.log (125000000000 / 470620994449) ∧
    -Real.log (125000000000 / 470620994449) ≤ (1325739351 / 1000000000) := by
  have h := checkLog_sound (w := (220620994449 / 720620994449)) (n := 12)
    (lo := (632592169 / 1000000000)) (hi := (63259217 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((470620994449 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(470620994449 / 250000000000) = 1/(125000000000 / 470620994449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14588 : Bounds (1325739349 / 1000000000) (1325739351 / 1000000000) (Real.log (470620994449 / 125000000000)) := by
  have h := reflection_log_14588_neg
  have he : Real.log (470620994449 / 125000000000) = -Real.log (125000000000 / 470620994449) := by
    rw [show ((470620994449 / 125000000000) : ℝ) = ((125000000000 / 470620994449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14589_neg : (3393475333 / 1000000000) ≤ -Real.log (100000000000 / 2976923076923) ∧
    -Real.log (100000000000 / 2976923076923) ≤ (1696737669 / 500000000) := by
  have h := checkLog_sound (w := (1376923076923 / 4576923076923)) (n := 12)
    (lo := (620886613 / 1000000000)) (hi := (310443307 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2976923076923 / 1600000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2976923076923 / 1600000000000) = 1/(100000000000 / 2976923076923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14589 : Bounds (3393475333 / 1000000000) (1696737669 / 500000000) (Real.log (2976923076923 / 100000000000)) := by
  have h := reflection_log_14589_neg
  have he : Real.log (2976923076923 / 100000000000) = -Real.log (100000000000 / 2976923076923) := by
    rw [show ((2976923076923 / 100000000000) : ℝ) = ((100000000000 / 2976923076923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14590_neg : (688455481 / 200000000) ≤ -Real.log (100000000000 / 3125806451613) ∧
    -Real.log (100000000000 / 3125806451613) ≤ (344227741 / 100000000) := by
  have h := checkLog_sound (w := (1525806451613 / 4725806451613)) (n := 12)
    (lo := (133937737 / 200000000)) (hi := (334844343 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125806451613 / 1600000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3125806451613 / 1600000000000) = 1/(100000000000 / 3125806451613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14590 : Bounds (688455481 / 200000000) (344227741 / 100000000) (Real.log (3125806451613 / 100000000000)) := by
  have h := reflection_log_14590_neg
  have he : Real.log (3125806451613 / 100000000000) = -Real.log (100000000000 / 3125806451613) := by
    rw [show ((3125806451613 / 100000000000) : ℝ) = ((100000000000 / 3125806451613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14591_neg : (82900413 / 125000000) ≤ -Real.log (1000 / 1941) ∧
    -Real.log (1000 / 1941) ≤ (132640661 / 200000000) := by
  have h := checkLog_sound (w := (941 / 2941)) (n := 12)
    (lo := (82900413 / 125000000)) (hi := (132640661 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1941 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1941 / 1000) = 1/(1000 / 1941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14591 : Bounds (82900413 / 125000000) (132640661 / 200000000) (Real.log (1941 / 1000)) := by
  have h := reflection_log_14591_neg
  have he : Real.log (1941 / 1000) = -Real.log (1000 / 1941) := by
    rw [show ((1941 / 1000) : ℝ) = ((1000 / 1941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0228 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_14592_neg : (353777229 / 125000000) ≤ -Real.log (59 / 1000) ∧
    -Real.log (59 / 1000) ≤ (2830217837 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 243)) (n := 12)
    (lo := (7203639 / 125000000)) (hi := (57629113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 118) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(125 / 118) = 1/(59 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14592 : Bounds (-2830217837 / 1000000000) (-353777229 / 125000000) (Real.log (59 / 1000)) := by
  have h := reflection_log_14592_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14593_neg : (940557 / 1000000000) ≤ -Real.log (1000000 / 1000941) ∧
    -Real.log (1000000 / 1000941) ≤ (470279 / 500000000) := by
  have h := checkLog_sound (w := (941 / 2000941)) (n := 12)
    (lo := (940557 / 1000000000)) (hi := (470279 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000941 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000941 / 1000000) = 1/(1000000 / 1000941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14593 : Bounds (940557 / 1000000000) (470279 / 500000000) (Real.log (1000941 / 1000000)) := by
  have h := reflection_log_14593_neg
  have he : Real.log (1000941 / 1000000) = -Real.log (1000000 / 1000941) := by
    rw [show ((1000941 / 1000000) : ℝ) = ((1000000 / 1000941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14594_neg : (941443 / 1000000000) ≤ -Real.log (999059 / 1000000) ∧
    -Real.log (999059 / 1000000) ≤ (235361 / 250000000) := by
  have h := checkLog_sound (w := (941 / 1999059)) (n := 12)
    (lo := (941443 / 1000000000)) (hi := (235361 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999059) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999059) = 1/(999059 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14594 : Bounds (-235361 / 250000000) (-941443 / 1000000000) (Real.log (999059 / 1000000)) := by
  have h := reflection_log_14594_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14595_neg : (91434963 / 200000000) ≤ -Real.log (200000 / 315921) ∧
    -Real.log (200000 / 315921) ≤ (14286713 / 31250000) := by
  have h := checkLog_sound (w := (115921 / 515921)) (n := 12)
    (lo := (91434963 / 200000000)) (hi := (14286713 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((315921 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(315921 / 200000) = 1/(200000 / 315921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14595 : Bounds (91434963 / 200000000) (14286713 / 31250000) (Real.log (315921 / 200000)) := by
  have h := reflection_log_14595_neg
  have he : Real.log (315921 / 200000) = -Real.log (200000 / 315921) := by
    rw [show ((315921 / 200000) : ℝ) = ((200000 / 315921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14596_neg : (216640133 / 250000000) ≤ -Real.log (84079 / 200000) ∧
    -Real.log (84079 / 200000) ≤ (433280267 / 500000000) := by
  have h := checkLog_sound (w := (15921 / 184079)) (n := 12)
    (lo := (21676669 / 125000000)) (hi := (173413353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 84079) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 84079) = 1/(84079 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14596 : Bounds (-433280267 / 500000000) (-216640133 / 250000000) (Real.log (84079 / 200000)) := by
  have h := reflection_log_14596_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14597_neg : (459580749 / 1000000000) ≤ -Real.log (100000 / 158341) ∧
    -Real.log (100000 / 158341) ≤ (1838323 / 4000000) := by
  have h := checkLog_sound (w := (58341 / 258341)) (n := 12)
    (lo := (459580749 / 1000000000)) (hi := (1838323 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((158341 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(158341 / 100000) = 1/(100000 / 158341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14597 : Bounds (459580749 / 1000000000) (1838323 / 4000000) (Real.log (158341 / 100000)) := by
  have h := reflection_log_14597_neg
  have he : Real.log (158341 / 100000) = -Real.log (100000 / 158341) := by
    rw [show ((158341 / 100000) : ℝ) = ((100000 / 158341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14598_neg : (875652753 / 1000000000) ≤ -Real.log (41659 / 100000) ∧
    -Real.log (41659 / 100000) ≤ (175130551 / 200000000) := by
  have h := checkLog_sound (w := (8341 / 91659)) (n := 12)
    (lo := (182505573 / 1000000000)) (hi := (91252787 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 41659) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 41659) = 1/(41659 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14598 : Bounds (-175130551 / 200000000) (-875652753 / 1000000000) (Real.log (41659 / 100000)) := by
  have h := reflection_log_14598_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14599_neg : (83214401 / 200000000) ≤ -Real.log (6596327719 / 10000000000) ∧
    -Real.log (6596327719 / 10000000000) ≤ (208036003 / 500000000) := by
  have h := checkLog_sound (w := (3403672281 / 16596327719)) (n := 12)
    (lo := (83214401 / 200000000)) (hi := (208036003 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 6596327719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 6596327719) = 1/(6596327719 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14599 : Bounds (-208036003 / 500000000) (-83214401 / 200000000) (Real.log (6596327719 / 10000000000)) := by
  have h := reflection_log_14599_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14600_neg : (409385717 / 1000000000) ≤ -Real.log (26562321759 / 40000000000) ∧
    -Real.log (26562321759 / 40000000000) ≤ (204692859 / 500000000) := by
  have h := checkLog_sound (w := (13437678241 / 66562321759)) (n := 12)
    (lo := (409385717 / 1000000000)) (hi := (204692859 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 26562321759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 26562321759) = 1/(26562321759 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14600 : Bounds (-204692859 / 500000000) (-409385717 / 1000000000) (Real.log (26562321759 / 40000000000)) := by
  have h := reflection_log_14600_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14601_neg : (330933837 / 250000000) ≤ -Real.log (50000000000 / 187871525589) ∧
    -Real.log (50000000000 / 187871525589) ≤ (26474707 / 20000000) := by
  have h := checkLog_sound (w := (87871525589 / 287871525589)) (n := 12)
    (lo := (78823521 / 125000000)) (hi := (630588169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((187871525589 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(187871525589 / 100000000000) = 1/(50000000000 / 187871525589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14601 : Bounds (330933837 / 250000000) (26474707 / 20000000) (Real.log (187871525589 / 50000000000)) := by
  have h := reflection_log_14601_neg
  have he : Real.log (187871525589 / 50000000000) = -Real.log (50000000000 / 187871525589) := by
    rw [show ((187871525589 / 50000000000) : ℝ) = ((50000000000 / 187871525589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14602_neg : (667616751 / 500000000) ≤ -Real.log (50000000000 / 190044168127) ∧
    -Real.log (50000000000 / 190044168127) ≤ (41726047 / 31250000) := by
  have h := checkLog_sound (w := (90044168127 / 290044168127)) (n := 12)
    (lo := (321043161 / 500000000)) (hi := (642086323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((190044168127 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(190044168127 / 100000000000) = 1/(50000000000 / 190044168127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14602 : Bounds (667616751 / 500000000) (41726047 / 31250000) (Real.log (190044168127 / 50000000000)) := by
  have h := reflection_log_14602_neg
  have he : Real.log (190044168127 / 50000000000) = -Real.log (50000000000 / 190044168127) := by
    rw [show ((190044168127 / 50000000000) : ℝ) = ((50000000000 / 190044168127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14603_neg : (688455481 / 200000000) ≤ -Real.log (31250000000 / 976814516129) ∧
    -Real.log (31250000000 / 976814516129) ≤ (344227741 / 100000000) := by
  have h := checkLog_sound (w := (476814516129 / 1476814516129)) (n := 12)
    (lo := (133937737 / 200000000)) (hi := (334844343 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976814516129 / 500000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(976814516129 / 500000000000) = 1/(31250000000 / 976814516129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14603 : Bounds (688455481 / 200000000) (344227741 / 100000000) (Real.log (976814516129 / 31250000000)) := by
  have h := reflection_log_14603_neg
  have he : Real.log (976814516129 / 31250000000) = -Real.log (31250000000 / 976814516129) := by
    rw [show ((976814516129 / 31250000000) : ℝ) = ((31250000000 / 976814516129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14604_neg : (218338821 / 62500000) ≤ -Real.log (500000000000 / 16449152542373) ∧
    -Real.log (500000000000 / 16449152542373) ≤ (1746710571 / 500000000) := by
  have h := checkLog_sound (w := (449152542373 / 32449152542373)) (n := 12)
    (lo := (6921309 / 250000000)) (hi := (27685237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16449152542373 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(16449152542373 / 16000000000000) = 1/(500000000000 / 16449152542373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14604 : Bounds (218338821 / 62500000) (1746710571 / 500000000) (Real.log (16449152542373 / 500000000000)) := by
  have h := reflection_log_14604_neg
  have he : Real.log (16449152542373 / 500000000000) = -Real.log (500000000000 / 16449152542373) := by
    rw [show ((16449152542373 / 500000000000) : ℝ) = ((500000000000 / 16449152542373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14605_neg : (332373853 / 500000000) ≤ -Real.log (125 / 243) ∧
    -Real.log (125 / 243) ≤ (664747707 / 1000000000) := by
  have h := checkLog_sound (w := (59 / 184)) (n := 12)
    (lo := (332373853 / 500000000)) (hi := (664747707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((243 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(243 / 125) = 1/(125 / 243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14605 : Bounds (332373853 / 500000000) (664747707 / 1000000000) (Real.log (243 / 125)) := by
  have h := reflection_log_14605_neg
  have he : Real.log (243 / 125) = -Real.log (125 / 243) := by
    rw [show ((243 / 125) : ℝ) = ((125 / 243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14606_neg : (1441201793 / 500000000) ≤ -Real.log (7 / 125) ∧
    -Real.log (7 / 125) ≤ (2882403591 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 237)) (n := 12)
    (lo := (54907433 / 500000000)) (hi := (109814867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 112) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(125 / 112) = 1/(7 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14606 : Bounds (-2882403591 / 1000000000) (-1441201793 / 500000000) (Real.log (7 / 125)) := by
  have h := reflection_log_14606_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14607_neg : (471777 / 500000000) ≤ -Real.log (62500 / 62559) ∧
    -Real.log (62500 / 62559) ≤ (188711 / 200000000) := by
  have h := checkLog_sound (w := (59 / 125059)) (n := 12)
    (lo := (471777 / 500000000)) (hi := (188711 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62559 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62559 / 62500) = 1/(62500 / 62559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14607 : Bounds (471777 / 500000000) (188711 / 200000000) (Real.log (62559 / 62500)) := by
  have h := reflection_log_14607_neg
  have he : Real.log (62559 / 62500) = -Real.log (62500 / 62559) := by
    rw [show ((62559 / 62500) : ℝ) = ((62500 / 62559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14608_neg : (188889 / 200000000) ≤ -Real.log (62441 / 62500) ∧
    -Real.log (62441 / 62500) ≤ (472223 / 500000000) := by
  have h := checkLog_sound (w := (59 / 124941)) (n := 12)
    (lo := (188889 / 200000000)) (hi := (472223 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 62441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 62441) = 1/(62441 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14608 : Bounds (-472223 / 500000000) (-188889 / 200000000) (Real.log (62441 / 62500)) := by
  have h := reflection_log_14608_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14609_neg : (459161313 / 1000000000) ≤ -Real.log (500000 / 791373) ∧
    -Real.log (500000 / 791373) ≤ (229580657 / 500000000) := by
  have h := checkLog_sound (w := (291373 / 1291373)) (n := 12)
    (lo := (459161313 / 1000000000)) (hi := (229580657 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((791373 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(791373 / 500000) = 1/(500000 / 791373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14609 : Bounds (459161313 / 1000000000) (229580657 / 500000000) (Real.log (791373 / 500000)) := by
  have h := reflection_log_14609_neg
  have he : Real.log (791373 / 500000) = -Real.log (500000 / 791373) := by
    rw [show ((791373 / 500000) : ℝ) = ((500000 / 791373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14610_neg : (874060129 / 1000000000) ≤ -Real.log (208627 / 500000) ∧
    -Real.log (208627 / 500000) ≤ (874060131 / 1000000000) := by
  have h := checkLog_sound (w := (41373 / 458627)) (n := 12)
    (lo := (180912949 / 1000000000)) (hi := (3618259 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 208627) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 208627) = 1/(208627 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14610 : Bounds (-874060131 / 1000000000) (-874060129 / 1000000000) (Real.log (208627 / 500000)) := by
  have h := reflection_log_14610_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14611_neg : (461583907 / 1000000000) ≤ -Real.log (200000 / 317317) ∧
    -Real.log (200000 / 317317) ≤ (115395977 / 250000000) := by
  have h := checkLog_sound (w := (117317 / 517317)) (n := 12)
    (lo := (461583907 / 1000000000)) (hi := (115395977 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((317317 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(317317 / 200000) = 1/(200000 / 317317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14611 : Bounds (461583907 / 1000000000) (115395977 / 250000000) (Real.log (317317 / 200000)) := by
  have h := reflection_log_14611_neg
  have he : Real.log (317317 / 200000) = -Real.log (200000 / 317317) := by
    rw [show ((317317 / 200000) : ℝ) = ((200000 / 317317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14612_neg : (883303347 / 1000000000) ≤ -Real.log (82683 / 200000) ∧
    -Real.log (82683 / 200000) ≤ (883303349 / 1000000000) := by
  have h := checkLog_sound (w := (17317 / 182683)) (n := 12)
    (lo := (190156167 / 1000000000)) (hi := (23769521 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 82683) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 82683) = 1/(82683 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14612 : Bounds (-883303349 / 1000000000) (-883303347 / 1000000000) (Real.log (82683 / 200000)) := by
  have h := reflection_log_14612_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14613_neg : (5271493 / 12500000) ≤ -Real.log (26236721511 / 40000000000) ∧
    -Real.log (26236721511 / 40000000000) ≤ (421719441 / 1000000000) := by
  have h := checkLog_sound (w := (13763278489 / 66236721511)) (n := 12)
    (lo := (5271493 / 12500000)) (hi := (421719441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 26236721511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 26236721511) = 1/(26236721511 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14613 : Bounds (-421719441 / 1000000000) (-5271493 / 12500000) (Real.log (26236721511 / 40000000000)) := by
  have h := reflection_log_14613_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14614_neg : (3241397 / 7812500) ≤ -Real.log (165101774871 / 250000000000) ∧
    -Real.log (165101774871 / 250000000000) ≤ (414898817 / 1000000000) := by
  have h := checkLog_sound (w := (84898225129 / 415101774871)) (n := 12)
    (lo := (3241397 / 7812500)) (hi := (414898817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 165101774871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 165101774871) = 1/(165101774871 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14614 : Bounds (-414898817 / 1000000000) (-3241397 / 7812500) (Real.log (165101774871 / 250000000000)) := by
  have h := reflection_log_14614_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14615_neg : (666610721 / 500000000) ≤ -Real.log (25000000000 / 94831086101) ∧
    -Real.log (25000000000 / 94831086101) ≤ (333305361 / 250000000) := by
  have h := checkLog_sound (w := (44831086101 / 144831086101)) (n := 12)
    (lo := (320037131 / 500000000)) (hi := (640074263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((94831086101 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(94831086101 / 50000000000) = 1/(25000000000 / 94831086101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14615 : Bounds (666610721 / 500000000) (333305361 / 250000000) (Real.log (94831086101 / 25000000000)) := by
  have h := reflection_log_14615_neg
  have he : Real.log (94831086101 / 25000000000) = -Real.log (25000000000 / 94831086101) := by
    rw [show ((94831086101 / 25000000000) : ℝ) = ((25000000000 / 94831086101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14616_neg : (268977451 / 200000000) ≤ -Real.log (500000000000 / 1918876915449) ∧
    -Real.log (500000000000 / 1918876915449) ≤ (1344887257 / 1000000000) := by
  have h := checkLog_sound (w := (918876915449 / 2918876915449)) (n := 12)
    (lo := (26069603 / 40000000)) (hi := (162935019 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1918876915449 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1918876915449 / 1000000000000) = 1/(500000000000 / 1918876915449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14616 : Bounds (268977451 / 200000000) (1344887257 / 1000000000) (Real.log (1918876915449 / 500000000000)) := by
  have h := reflection_log_14616_neg
  have he : Real.log (1918876915449 / 500000000000) = -Real.log (500000000000 / 1918876915449) := by
    rw [show ((1918876915449 / 500000000000) : ℝ) = ((500000000000 / 1918876915449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14617_neg : (218338821 / 62500000) ≤ -Real.log (125000000000 / 4112288135593) ∧
    -Real.log (125000000000 / 4112288135593) ≤ (1746710571 / 500000000) := by
  have h := checkLog_sound (w := (112288135593 / 8112288135593)) (n := 12)
    (lo := (6921309 / 250000000)) (hi := (27685237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4112288135593 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(4112288135593 / 4000000000000) = 1/(125000000000 / 4112288135593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14617 : Bounds (218338821 / 62500000) (1746710571 / 500000000) (Real.log (4112288135593 / 125000000000)) := by
  have h := reflection_log_14617_neg
  have he : Real.log (4112288135593 / 125000000000) = -Real.log (125000000000 / 4112288135593) := by
    rw [show ((4112288135593 / 125000000000) : ℝ) = ((125000000000 / 4112288135593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14618_neg : (3547151291 / 1000000000) ≤ -Real.log (500000000000 / 17357142857143) ∧
    -Real.log (500000000000 / 17357142857143) ≤ (3547151297 / 1000000000) := by
  have h := checkLog_sound (w := (1357142857143 / 33357142857143)) (n := 12)
    (lo := (81415391 / 1000000000)) (hi := (2544231 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17357142857143 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(17357142857143 / 16000000000000) = 1/(500000000000 / 17357142857143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14618 : Bounds (3547151291 / 1000000000) (3547151297 / 1000000000) (Real.log (17357142857143 / 500000000000)) := by
  have h := reflection_log_14618_neg
  have he : Real.log (17357142857143 / 500000000000) = -Real.log (500000000000 / 17357142857143) := by
    rw [show ((17357142857143 / 500000000000) : ℝ) = ((500000000000 / 17357142857143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14619_neg : (333144863 / 500000000) ≤ -Real.log (1000 / 1947) ∧
    -Real.log (1000 / 1947) ≤ (666289727 / 1000000000) := by
  have h := checkLog_sound (w := (947 / 2947)) (n := 12)
    (lo := (333144863 / 500000000)) (hi := (666289727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1947 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1947 / 1000) = 1/(1000 / 1947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14619 : Bounds (333144863 / 500000000) (666289727 / 1000000000) (Real.log (1947 / 1000)) := by
  have h := reflection_log_14619_neg
  have he : Real.log (1947 / 1000) = -Real.log (1000 / 1947) := by
    rw [show ((1947 / 1000) : ℝ) = ((1000 / 1947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14620_neg : (2937463363 / 1000000000) ≤ -Real.log (53 / 1000) ∧
    -Real.log (53 / 1000) ≤ (367182921 / 125000000) := by
  have h := checkLog_sound (w := (19 / 231)) (n := 12)
    (lo := (164874643 / 1000000000)) (hi := (41218661 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 106) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(125 / 106) = 1/(53 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14620 : Bounds (-367182921 / 125000000) (-2937463363 / 1000000000) (Real.log (53 / 1000)) := by
  have h := reflection_log_14620_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14621_neg : (946551 / 1000000000) ≤ -Real.log (1000000 / 1000947) ∧
    -Real.log (1000000 / 1000947) ≤ (118319 / 125000000) := by
  have h := checkLog_sound (w := (947 / 2000947)) (n := 12)
    (lo := (946551 / 1000000000)) (hi := (118319 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000947 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000947 / 1000000) = 1/(1000000 / 1000947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14621 : Bounds (946551 / 1000000000) (118319 / 125000000) (Real.log (1000947 / 1000000)) := by
  have h := reflection_log_14621_neg
  have he : Real.log (1000947 / 1000000) = -Real.log (1000000 / 1000947) := by
    rw [show ((1000947 / 1000000) : ℝ) = ((1000000 / 1000947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14622_neg : (118431 / 125000000) ≤ -Real.log (999053 / 1000000) ∧
    -Real.log (999053 / 1000000) ≤ (947449 / 1000000000) := by
  have h := checkLog_sound (w := (947 / 1999053)) (n := 12)
    (lo := (118431 / 125000000)) (hi := (947449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999053) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999053) = 1/(999053 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14622 : Bounds (-947449 / 1000000000) (-118431 / 125000000) (Real.log (999053 / 1000000)) := by
  have h := reflection_log_14622_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14623_neg : (461165941 / 1000000000) ≤ -Real.log (500000 / 792961) ∧
    -Real.log (500000 / 792961) ≤ (230582971 / 500000000) := by
  have h := checkLog_sound (w := (292961 / 1292961)) (n := 12)
    (lo := (461165941 / 1000000000)) (hi := (230582971 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((792961 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(792961 / 500000) = 1/(500000 / 792961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14623 : Bounds (461165941 / 1000000000) (230582971 / 500000000) (Real.log (792961 / 500000)) := by
  have h := reflection_log_14623_neg
  have he : Real.log (792961 / 500000) = -Real.log (500000 / 792961) := by
    rw [show ((792961 / 500000) : ℝ) = ((500000 / 792961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14624_neg : (220425229 / 250000000) ≤ -Real.log (207039 / 500000) ∧
    -Real.log (207039 / 500000) ≤ (440850459 / 500000000) := by
  have h := checkLog_sound (w := (42961 / 457039)) (n := 12)
    (lo := (23569217 / 125000000)) (hi := (188553737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 207039) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 207039) = 1/(207039 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14624 : Bounds (-440850459 / 500000000) (-220425229 / 250000000) (Real.log (207039 / 500000)) := by
  have h := reflection_log_14624_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14625_neg : (115901741 / 250000000) ≤ -Real.log (500000 / 794899) ∧
    -Real.log (500000 / 794899) ≤ (92721393 / 200000000) := by
  have h := checkLog_sound (w := (294899 / 1294899)) (n := 12)
    (lo := (115901741 / 250000000)) (hi := (92721393 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((794899 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(794899 / 500000) = 1/(500000 / 794899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14625 : Bounds (115901741 / 250000000) (92721393 / 200000000) (Real.log (794899 / 500000)) := by
  have h := reflection_log_14625_neg
  have he : Real.log (794899 / 500000) = -Real.log (500000 / 794899) := by
    rw [show ((794899 / 500000) : ℝ) = ((500000 / 794899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14626_neg : (891105557 / 1000000000) ≤ -Real.log (205101 / 500000) ∧
    -Real.log (205101 / 500000) ≤ (891105559 / 1000000000) := by
  have h := checkLog_sound (w := (44899 / 455101)) (n := 12)
    (lo := (197958377 / 1000000000)) (hi := (98979189 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 205101) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 205101) = 1/(205101 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14626 : Bounds (-891105559 / 1000000000) (-891105557 / 1000000000) (Real.log (205101 / 500000)) := by
  have h := reflection_log_14626_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14627_neg : (427498593 / 1000000000) ≤ -Real.log (163034579799 / 250000000000) ∧
    -Real.log (163034579799 / 250000000000) ≤ (213749297 / 500000000) := by
  have h := checkLog_sound (w := (86965420201 / 413034579799)) (n := 12)
    (lo := (427498593 / 1000000000)) (hi := (213749297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 163034579799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 163034579799) = 1/(163034579799 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14627 : Bounds (-213749297 / 500000000) (-427498593 / 1000000000) (Real.log (163034579799 / 250000000000)) := by
  have h := reflection_log_14627_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14628_neg : (16821399 / 40000000) ≤ -Real.log (164173852479 / 250000000000) ∧
    -Real.log (164173852479 / 250000000000) ≤ (6570859 / 15625000) := by
  have h := checkLog_sound (w := (85826147521 / 414173852479)) (n := 12)
    (lo := (16821399 / 40000000)) (hi := (6570859 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 164173852479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 164173852479) = 1/(164173852479 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14628 : Bounds (-6570859 / 15625000) (-16821399 / 40000000) (Real.log (164173852479 / 250000000000)) := by
  have h := reflection_log_14628_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14629_neg : (671433429 / 500000000) ≤ -Real.log (62500000000 / 239375492057) ∧
    -Real.log (62500000000 / 239375492057) ≤ (67143343 / 50000000) := by
  have h := checkLog_sound (w := (114375492057 / 364375492057)) (n := 12)
    (lo := (324859839 / 500000000)) (hi := (649719679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((239375492057 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(239375492057 / 125000000000) = 1/(62500000000 / 239375492057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14629 : Bounds (671433429 / 500000000) (67143343 / 50000000) (Real.log (239375492057 / 62500000000)) := by
  have h := reflection_log_14629_neg
  have he : Real.log (239375492057 / 62500000000) = -Real.log (62500000000 / 239375492057) := by
    rw [show ((239375492057 / 62500000000) : ℝ) = ((62500000000 / 239375492057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14630_neg : (1354712521 / 1000000000) ≤ -Real.log (250000000000 / 968911658159) ∧
    -Real.log (250000000000 / 968911658159) ≤ (1354712523 / 1000000000) := by
  have h := checkLog_sound (w := (468911658159 / 1468911658159)) (n := 12)
    (lo := (661565341 / 1000000000)) (hi := (330782671 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((968911658159 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(968911658159 / 500000000000) = 1/(250000000000 / 968911658159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14630 : Bounds (1354712521 / 1000000000) (1354712523 / 1000000000) (Real.log (968911658159 / 250000000000)) := by
  have h := reflection_log_14630_neg
  have he : Real.log (968911658159 / 250000000000) = -Real.log (250000000000 / 968911658159) := by
    rw [show ((968911658159 / 250000000000) : ℝ) = ((250000000000 / 968911658159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14631_neg : (3547151291 / 1000000000) ≤ -Real.log (250000000000 / 8678571428571) ∧
    -Real.log (250000000000 / 8678571428571) ≤ (3547151297 / 1000000000) := by
  have h := checkLog_sound (w := (678571428571 / 16678571428571)) (n := 12)
    (lo := (81415391 / 1000000000)) (hi := (2544231 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8678571428571 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(8678571428571 / 8000000000000) = 1/(250000000000 / 8678571428571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14631 : Bounds (3547151291 / 1000000000) (3547151297 / 1000000000) (Real.log (8678571428571 / 250000000000)) := by
  have h := reflection_log_14631_neg
  have he : Real.log (8678571428571 / 250000000000) = -Real.log (250000000000 / 8678571428571) := by
    rw [show ((8678571428571 / 250000000000) : ℝ) = ((250000000000 / 8678571428571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14632_neg : (3603753089 / 1000000000) ≤ -Real.log (250000000000 / 9183962264151) ∧
    -Real.log (250000000000 / 9183962264151) ≤ (720750619 / 200000000) := by
  have h := checkLog_sound (w := (1183962264151 / 17183962264151)) (n := 12)
    (lo := (138017189 / 1000000000)) (hi := (13801719 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9183962264151 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(9183962264151 / 8000000000000) = 1/(250000000000 / 9183962264151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14632 : Bounds (3603753089 / 1000000000) (720750619 / 200000000) (Real.log (9183962264151 / 250000000000)) := by
  have h := reflection_log_14632_neg
  have he : Real.log (9183962264151 / 250000000000) = -Real.log (250000000000 / 9183962264151) := by
    rw [show ((9183962264151 / 250000000000) : ℝ) = ((250000000000 / 9183962264151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14633_neg : (166957343 / 250000000) ≤ -Real.log (20 / 39) ∧
    -Real.log (20 / 39) ≤ (667829373 / 1000000000) := by
  have h := checkLog_sound (w := (19 / 59)) (n := 12)
    (lo := (166957343 / 250000000)) (hi := (667829373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39 / 20) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39 / 20) = 1/(20 / 39) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14633 : Bounds (166957343 / 250000000) (667829373 / 1000000000) (Real.log (39 / 20)) := by
  have h := reflection_log_14633_neg
  have he : Real.log (39 / 20) = -Real.log (20 / 39) := by
    rw [show ((39 / 20) : ℝ) = ((20 / 39) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14634_neg : (2995732271 / 1000000000) ≤ -Real.log (1 / 20) ∧
    -Real.log (1 / 20) ≤ (748933069 / 250000000) := by
  have h := checkLog_sound (w := (1 / 9)) (n := 12)
    (lo := (223143551 / 1000000000)) (hi := (1743309 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 4) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(5 / 4) = 1/(1 / 20) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14634 : Bounds (-748933069 / 250000000) (-2995732271 / 1000000000) (Real.log (1 / 20)) := by
  have h := reflection_log_14634_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14635_neg : (949549 / 1000000000) ≤ -Real.log (20000 / 20019) ∧
    -Real.log (20000 / 20019) ≤ (18991 / 20000000) := by
  have h := checkLog_sound (w := (19 / 40019)) (n := 12)
    (lo := (949549 / 1000000000)) (hi := (18991 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20019 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20019 / 20000) = 1/(20000 / 20019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14635 : Bounds (949549 / 1000000000) (18991 / 20000000) (Real.log (20019 / 20000)) := by
  have h := reflection_log_14635_neg
  have he : Real.log (20019 / 20000) = -Real.log (20000 / 20019) := by
    rw [show ((20019 / 20000) : ℝ) = ((20000 / 20019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14636_neg : (950451 / 1000000000) ≤ -Real.log (19981 / 20000) ∧
    -Real.log (19981 / 20000) ≤ (237613 / 250000000) := by
  have h := checkLog_sound (w := (19 / 39981)) (n := 12)
    (lo := (950451 / 1000000000)) (hi := (237613 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 19981) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 19981) = 1/(19981 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14636 : Bounds (-237613 / 250000000) (-950451 / 1000000000) (Real.log (19981 / 20000)) := by
  have h := reflection_log_14636_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14637_neg : (463191101 / 1000000000) ≤ -Real.log (1000000 / 1589137) ∧
    -Real.log (1000000 / 1589137) ≤ (231595551 / 500000000) := by
  have h := checkLog_sound (w := (589137 / 2589137)) (n := 12)
    (lo := (463191101 / 1000000000)) (hi := (231595551 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1589137 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1589137 / 1000000) = 1/(1000000 / 1589137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14637 : Bounds (463191101 / 1000000000) (231595551 / 500000000) (Real.log (1589137 / 1000000)) := by
  have h := reflection_log_14637_neg
  have he : Real.log (1589137 / 1000000) = -Real.log (1000000 / 1589137) := by
    rw [show ((1589137 / 1000000) : ℝ) = ((1000000 / 1589137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14638_neg : (222373863 / 250000000) ≤ -Real.log (410863 / 1000000) ∧
    -Real.log (410863 / 1000000) ≤ (444747727 / 500000000) := by
  have h := checkLog_sound (w := (89137 / 910863)) (n := 12)
    (lo := (12271767 / 62500000)) (hi := (196348273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 410863) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 410863) = 1/(410863 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14638 : Bounds (-444747727 / 500000000) (-222373863 / 250000000) (Real.log (410863 / 1000000)) := by
  have h := reflection_log_14638_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14639_neg : (93130209 / 200000000) ≤ -Real.log (1000000 / 1593051) ∧
    -Real.log (1000000 / 1593051) ≤ (232825523 / 500000000) := by
  have h := checkLog_sound (w := (593051 / 2593051)) (n := 12)
    (lo := (93130209 / 200000000)) (hi := (232825523 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1593051 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1593051 / 1000000) = 1/(1000000 / 1593051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14639 : Bounds (93130209 / 200000000) (232825523 / 500000000) (Real.log (1593051 / 1000000)) := by
  have h := reflection_log_14639_neg
  have he : Real.log (1593051 / 1000000) = -Real.log (1000000 / 1593051) := by
    rw [show ((1593051 / 1000000) : ℝ) = ((1000000 / 1593051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14640_neg : (899067407 / 1000000000) ≤ -Real.log (406949 / 1000000) ∧
    -Real.log (406949 / 1000000) ≤ (899067409 / 1000000000) := by
  have h := checkLog_sound (w := (93051 / 906949)) (n := 12)
    (lo := (205920227 / 1000000000)) (hi := (51480057 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 406949) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 406949) = 1/(406949 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14640 : Bounds (-899067409 / 1000000000) (-899067407 / 1000000000) (Real.log (406949 / 1000000)) := by
  have h := reflection_log_14640_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14641_neg : (433416363 / 1000000000) ≤ -Real.log (648290511399 / 1000000000000) ∧
    -Real.log (648290511399 / 1000000000000) ≤ (108354091 / 250000000) := by
  have h := checkLog_sound (w := (351709488601 / 1648290511399)) (n := 12)
    (lo := (433416363 / 1000000000)) (hi := (108354091 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 648290511399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 648290511399) = 1/(648290511399 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14641 : Bounds (-108354091 / 250000000) (-433416363 / 1000000000) (Real.log (648290511399 / 1000000000000)) := by
  have h := reflection_log_14641_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14642_neg : (426304351 / 1000000000) ≤ -Real.log (652917595231 / 1000000000000) ∧
    -Real.log (652917595231 / 1000000000000) ≤ (13322011 / 31250000) := by
  have h := checkLog_sound (w := (347082404769 / 1652917595231)) (n := 12)
    (lo := (426304351 / 1000000000)) (hi := (13322011 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 652917595231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 652917595231) = 1/(652917595231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14642 : Bounds (-13322011 / 31250000) (-426304351 / 1000000000) (Real.log (652917595231 / 1000000000000)) := by
  have h := reflection_log_14642_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14643_neg : (676343277 / 500000000) ≤ -Real.log (125000000000 / 483475331193) ∧
    -Real.log (125000000000 / 483475331193) ≤ (338171639 / 250000000) := by
  have h := checkLog_sound (w := (233475331193 / 733475331193)) (n := 12)
    (lo := (329769687 / 500000000)) (hi := (1055263 / 1600000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((483475331193 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(483475331193 / 250000000000) = 1/(125000000000 / 483475331193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14643 : Bounds (676343277 / 500000000) (338171639 / 250000000) (Real.log (483475331193 / 125000000000)) := by
  have h := reflection_log_14643_neg
  have he : Real.log (483475331193 / 125000000000) = -Real.log (125000000000 / 483475331193) := by
    rw [show ((483475331193 / 125000000000) : ℝ) = ((125000000000 / 483475331193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14644_neg : (1364718453 / 1000000000) ≤ -Real.log (250000000000 / 978655187751) ∧
    -Real.log (250000000000 / 978655187751) ≤ (272943691 / 200000000) := by
  have h := checkLog_sound (w := (478655187751 / 1478655187751)) (n := 12)
    (lo := (671571273 / 1000000000)) (hi := (335785637 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((978655187751 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(978655187751 / 500000000000) = 1/(250000000000 / 978655187751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14644 : Bounds (1364718453 / 1000000000) (272943691 / 200000000) (Real.log (978655187751 / 250000000000)) := by
  have h := reflection_log_14644_neg
  have he : Real.log (978655187751 / 250000000000) = -Real.log (250000000000 / 978655187751) := by
    rw [show ((978655187751 / 250000000000) : ℝ) = ((250000000000 / 978655187751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14645_neg : (3603753089 / 1000000000) ≤ -Real.log (500000000000 / 18367924528301) ∧
    -Real.log (500000000000 / 18367924528301) ≤ (720750619 / 200000000) := by
  have h := checkLog_sound (w := (2367924528301 / 34367924528301)) (n := 12)
    (lo := (138017189 / 1000000000)) (hi := (13801719 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18367924528301 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(18367924528301 / 16000000000000) = 1/(500000000000 / 18367924528301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14645 : Bounds (3603753089 / 1000000000) (720750619 / 200000000) (Real.log (18367924528301 / 500000000000)) := by
  have h := reflection_log_14645_neg
  have he : Real.log (18367924528301 / 500000000000) = -Real.log (500000000000 / 18367924528301) := by
    rw [show ((18367924528301 / 500000000000) : ℝ) = ((500000000000 / 18367924528301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14646_neg : (3663561643 / 1000000000) ≤ -Real.log (1 / 39) ∧
    -Real.log (1 / 39) ≤ (3663561649 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 71)) (n := 12)
    (lo := (197825743 / 1000000000)) (hi := (12364109 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39 / 32) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(39 / 32) = 1/(1 / 39) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14646 : Bounds (3663561643 / 1000000000) (3663561649 / 1000000000) (Real.log (39 / 1)) := by
  have h := reflection_log_14646_neg
  have he : Real.log (39 / 1) = -Real.log (1 / 39) := by
    rw [show ((39 / 1) : ℝ) = ((1 / 39) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14647_neg : (668342061 / 1000000000) ≤ -Real.log (1000 / 1951) ∧
    -Real.log (1000 / 1951) ≤ (334171031 / 500000000) := by
  have h := checkLog_sound (w := (951 / 2951)) (n := 12)
    (lo := (668342061 / 1000000000)) (hi := (334171031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1951 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1951 / 1000) = 1/(1000 / 1951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14647 : Bounds (668342061 / 1000000000) (334171031 / 500000000) (Real.log (1951 / 1000)) := by
  have h := reflection_log_14647_neg
  have he : Real.log (1951 / 1000) = -Real.log (1000 / 1951) := by
    rw [show ((1951 / 1000) : ℝ) = ((1000 / 1951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14648_neg : (1507967489 / 500000000) ≤ -Real.log (49 / 1000) ∧
    -Real.log (49 / 1000) ≤ (3015934983 / 1000000000) := by
  have h := checkLog_sound (w := (27 / 223)) (n := 12)
    (lo := (121673129 / 500000000)) (hi := (243346259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 98) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(125 / 98) = 1/(49 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14648 : Bounds (-3015934983 / 1000000000) (-1507967489 / 500000000) (Real.log (49 / 1000)) := by
  have h := reflection_log_14648_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14649_neg : (237637 / 250000000) ≤ -Real.log (1000000 / 1000951) ∧
    -Real.log (1000000 / 1000951) ≤ (950549 / 1000000000) := by
  have h := checkLog_sound (w := (951 / 2000951)) (n := 12)
    (lo := (237637 / 250000000)) (hi := (950549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000951 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000951 / 1000000) = 1/(1000000 / 1000951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14649 : Bounds (237637 / 250000000) (950549 / 1000000000) (Real.log (1000951 / 1000000)) := by
  have h := reflection_log_14649_neg
  have he : Real.log (1000951 / 1000000) = -Real.log (1000000 / 1000951) := by
    rw [show ((1000951 / 1000000) : ℝ) = ((1000000 / 1000951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14650_neg : (237863 / 250000000) ≤ -Real.log (999049 / 1000000) ∧
    -Real.log (999049 / 1000000) ≤ (951453 / 1000000000) := by
  have h := checkLog_sound (w := (951 / 1999049)) (n := 12)
    (lo := (237863 / 250000000)) (hi := (951453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999049) = 1/(999049 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14650 : Bounds (-951453 / 1000000000) (-237863 / 250000000) (Real.log (999049 / 1000000)) := by
  have h := reflection_log_14650_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14651_neg : (23261833 / 50000000) ≤ -Real.log (1000000 / 1592391) ∧
    -Real.log (1000000 / 1592391) ≤ (465236661 / 1000000000) := by
  have h := checkLog_sound (w := (592391 / 2592391)) (n := 12)
    (lo := (23261833 / 50000000)) (hi := (465236661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1592391 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1592391 / 1000000) = 1/(1000000 / 1592391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14651 : Bounds (23261833 / 50000000) (465236661 / 1000000000) (Real.log (1592391 / 1000000)) := by
  have h := reflection_log_14651_neg
  have he : Real.log (1592391 / 1000000) = -Real.log (1000000 / 1592391) := by
    rw [show ((1592391 / 1000000) : ℝ) = ((1000000 / 1592391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14652_neg : (56090431 / 62500000) ≤ -Real.log (407609 / 1000000) ∧
    -Real.log (407609 / 1000000) ≤ (448723449 / 500000000) := by
  have h := checkLog_sound (w := (92391 / 907609)) (n := 12)
    (lo := (51074929 / 250000000)) (hi := (204299717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 407609) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 407609) = 1/(407609 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14652 : Bounds (-448723449 / 500000000) (-56090431 / 62500000) (Real.log (407609 / 1000000)) := by
  have h := reflection_log_14652_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14653_neg : (233168771 / 500000000) ≤ -Real.log (200000 / 318829) ∧
    -Real.log (200000 / 318829) ≤ (466337543 / 1000000000) := by
  have h := checkLog_sound (w := (118829 / 518829)) (n := 12)
    (lo := (233168771 / 500000000)) (hi := (466337543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((318829 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(318829 / 200000) = 1/(200000 / 318829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14653 : Bounds (233168771 / 500000000) (466337543 / 1000000000) (Real.log (318829 / 200000)) := by
  have h := reflection_log_14653_neg
  have he : Real.log (318829 / 200000) = -Real.log (200000 / 318829) := by
    rw [show ((318829 / 200000) : ℝ) = ((200000 / 318829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14654_neg : (36070373 / 40000000) ≤ -Real.log (81171 / 200000) ∧
    -Real.log (81171 / 200000) ≤ (901759327 / 1000000000) := by
  have h := checkLog_sound (w := (18829 / 181171)) (n := 12)
    (lo := (41722429 / 200000000)) (hi := (104306073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 81171) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 81171) = 1/(81171 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14654 : Bounds (-901759327 / 1000000000) (-36070373 / 40000000) (Real.log (81171 / 200000)) := by
  have h := reflection_log_14654_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14655_neg : (435421783 / 1000000000) ≤ -Real.log (25879668759 / 40000000000) ∧
    -Real.log (25879668759 / 40000000000) ≤ (54427723 / 125000000) := by
  have h := checkLog_sound (w := (14120331241 / 65879668759)) (n := 12)
    (lo := (435421783 / 1000000000)) (hi := (54427723 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 25879668759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 25879668759) = 1/(25879668759 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14655 : Bounds (-54427723 / 125000000) (-435421783 / 1000000000) (Real.log (25879668759 / 40000000000)) := by
  have h := reflection_log_14655_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end


