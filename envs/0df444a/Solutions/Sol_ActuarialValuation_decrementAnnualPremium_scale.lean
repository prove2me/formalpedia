-- Prove2me | solution 1 for ActuarialValuation.decrementAnnualPremium_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T14:51:22.657986+00:00
-- url     : https://prove2.me/submissions/732bbe9b-9ef5-4457-aafe-8b118d3de059

import Mathlib
import Definitions.Def_actuarial_decrementAnnualPremium
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {J : Type*} [Fintype J] (p : ℝ) (q b : J → ℝ) (v R Rnext : ℝ) (a : ℝ)
  :
  decrementAnnualPremium p q (fun j => a * b j) v (a * R) (a * Rnext) =
    a * decrementAnnualPremium p q b v R Rnext := by
  classical
  have hsum : (∑ j : J, q j * (a * b j)) =
      a * (∑ j : J, q j * b j) := by
    calc
      (∑ j : J, q j * (a * b j)) =
          ∑ j : J, a * (q j * b j) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = a * (∑ j : J, q j * b j) := by rw [Finset.mul_sum]
  change v * (p * (a * Rnext) + (∑ j : J, q j * (a * b j))) - a * R =
    a * (v * (p * Rnext + (∑ j : J, q j * b j)) - R)
  rw [hsum]
  ring
