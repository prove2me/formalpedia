-- Prove2me | solution 1 for ActuarialValuation.panjerRecurrence_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:17:47.191708+00:00
-- url     : https://prove2.me/submissions/dcb03c57-90e6-41d7-b868-84437987b31c

import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerRecurrenceLaw

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (lambda : ℝ) (f g : ℕ → ℝ) (hl : 0 ≤ lambda) (hf : ∀ j, 0 ≤ f j) (hg : panjerRecurrenceLaw lambda f g) : ∀ k : ℕ, 0 ≤ g k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero =>
      rw [hg.1]
      exact le_of_lt (Real.exp_pos _)
    | succ k =>
      rw [hg.2 k]
      unfold panjerRecursionStep
      apply mul_nonneg
      · apply div_nonneg hl
        positivity
      · apply Finset.sum_nonneg
        intro j hj
        unfold panjerWeightedSeverity
        apply mul_nonneg
        · exact mul_nonneg (by positivity) (hf (j + 1))
        · exact ih (k - j) (Nat.lt_succ_of_le (Nat.sub_le k j))
