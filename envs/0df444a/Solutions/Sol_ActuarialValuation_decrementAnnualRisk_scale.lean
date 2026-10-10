-- Prove2me | solution 1 for ActuarialValuation.decrementAnnualRisk_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:35:38.739397+00:00
-- url     : https://prove2.me/submissions/4eebe467-43b3-4abd-a184-96afccb197e9

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_decrementAnnualRisk
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {C : Type*} [Fintype C]
  (w rho : ℕ → C → ℝ) (a : ℝ) (t : ℕ) :
  decrementAnnualRisk w (fun n c => a * rho n c) t =
    a ^ 2 * decrementAnnualRisk w rho t := by
  unfold decrementAnnualRisk
  have h1 : (∑ c : C, w t c * (a * rho t c) ^ 2) =
      a ^ 2 * (∑ c : C, w t c * (rho t c) ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    ring
  have h2 : (∑ c : C, w t c * (a * rho t c)) =
      a * (∑ c : C, w t c * rho t c) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    ring
  rw [h1, h2]
  ring
