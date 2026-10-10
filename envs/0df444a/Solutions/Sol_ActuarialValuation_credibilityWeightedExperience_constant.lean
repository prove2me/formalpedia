-- Prove2me | solution 1 for ActuarialValuation.credibilityWeightedExperience_constant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:51:46.688958+00:00
-- url     : https://prove2.me/submissions/d9f33d65-be80-4c19-ae7a-b97e954987c5

import Mathlib
import Definitions.Def_actuarial_credibilityWeightedExperience
import Definitions.Def_actuarial_credibilityExposureTotal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (p : ℕ → ℝ) (n : ℕ) (c : ℝ)
  (hpos : credibilityExposureTotal p n ≠ 0) :
  credibilityWeightedExperience p (fun _ => c) n = c := by
  unfold credibilityWeightedExperience credibilityExposureTotal
  rw [← Finset.sum_mul]
  simp only [credibilityExposureTotal] at hpos
  rw [div_eq_iff hpos]
  ring
