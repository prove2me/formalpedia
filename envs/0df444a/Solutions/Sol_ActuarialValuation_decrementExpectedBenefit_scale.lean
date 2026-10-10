-- Prove2me | solution 1 for ActuarialValuation.decrementExpectedBenefit_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T14:51:16.147894+00:00
-- url     : https://prove2.me/submissions/52f1d2b4-8bf4-4bb7-bccc-91fb288da477

import Mathlib
import Definitions.Def_actuarial_decrementExpectedBenefit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {J : Type*} [Fintype J] (q b : J → ℝ) (a : ℝ)
  :
  decrementExpectedBenefit q (fun j => a * b j) = a * decrementExpectedBenefit q b := by
  classical
  change (∑ j : J, q j * (a * b j)) = a * (∑ j : J, q j * b j)
  calc
    (∑ j : J, q j * (a * b j)) =
      ∑ j : J, a * (q j * b j) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
    _ = a * (∑ j : J, q j * b j) := by rw [Finset.mul_sum]
