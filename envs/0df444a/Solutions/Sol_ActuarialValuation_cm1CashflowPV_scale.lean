-- Prove2me | solution 1 for ActuarialValuation.cm1CashflowPV_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:15:34.75511+00:00
-- url     : https://prove2.me/submissions/e9c666b4-f099-4d7b-9198-32b4344a65b3

import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1CashflowPV
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a : ℕ → ℝ) (n : ℕ) (i c : ℝ) : cm1CashflowPV (fun k => c*a k) n i = c * cm1CashflowPV a n i := by
  unfold cm1CashflowPV
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring
