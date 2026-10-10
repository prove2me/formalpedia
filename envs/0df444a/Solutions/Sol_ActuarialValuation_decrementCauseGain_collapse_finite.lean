-- Prove2me | solution 1 for ActuarialValuation.decrementCauseGain_collapse_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:03:20.95698+00:00
-- url     : https://prove2.me/submissions/4d6eb597-04aa-4d31-8377-efbf9c2caecb

import Mathlib
import Definitions.Def_actuarial_decrementCauseInnovation
import Definitions.Def_actuarial_decrementTailMass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
    {C : Type*} [Fintype C] (w rho : ℕ → C → ℝ)
    (t k : ℕ) (d : C) :
    (∑ c : C, rho t c * ActuarialValuation.decrementCauseInnovation w t c k d) =
    (if k = t then rho t d else 0) -
      ((∑ c : C, w t c * rho t c) /
        ActuarialValuation.decrementTailMass w t) *
        (if t ≤ k then (1 : ℝ) else 0) := by
  classical
  change (∑ c : C, rho t c *
      ((if k = t ∧ d = c then (1 : ℝ) else 0) -
        (w t c / ActuarialValuation.decrementTailMass w t) *
          (if t ≤ k then (1 : ℝ) else 0))) =
    (if k = t then rho t d else 0) -
      ((∑ c : C, w t c * rho t c) /
        ActuarialValuation.decrementTailMass w t) *
        (if t ≤ k then (1 : ℝ) else 0)
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hfirst :
      (∑ c : C, rho t c * (if k = t ∧ d = c then (1 : ℝ) else 0)) =
      (if k = t then rho t d else 0) := by
    by_cases hk : k = t
    · simp [hk]
    · simp [hk]
  have hsecond :
      (∑ c : C, rho t c *
        ((w t c / ActuarialValuation.decrementTailMass w t) *
          (if t ≤ k then (1 : ℝ) else 0))) =
      ((∑ c : C, w t c * rho t c) /
        ActuarialValuation.decrementTailMass w t) *
        (if t ≤ k then (1 : ℝ) else 0) := by
    by_cases ht : t ≤ k
    · simp only [if_pos ht, mul_one]
      calc
        (∑ c : C, rho t c *
            (w t c / ActuarialValuation.decrementTailMass w t)) =
          ∑ c : C, (w t c * rho t c) /
            ActuarialValuation.decrementTailMass w t := by
              apply Finset.sum_congr rfl
              intro c _
              ring
        _ = (∑ c : C, w t c * rho t c) /
            ActuarialValuation.decrementTailMass w t := by
              rw [Finset.sum_div]
    · simp [ht]
  rw [hfirst,hsecond]
