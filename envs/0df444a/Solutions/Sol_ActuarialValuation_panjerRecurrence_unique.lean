-- Prove2me | solution 1 for ActuarialValuation.panjerRecurrence_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:16:24.759973+00:00
-- url     : https://prove2.me/submissions/13683720-3b70-4202-b191-d01c5611f3ba

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerRecurrenceLaw

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (lambda : ℝ) (f g h : ℕ → ℝ) (hg : panjerRecurrenceLaw lambda f g) (hh : panjerRecurrenceLaw lambda f h) : ∀ k : ℕ, g k = h k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero =>
      exact hg.1.trans hh.1.symm
    | succ k =>
      calc
        g (k + 1) = panjerRecursionStep lambda f g k := hg.2 k
        _ = panjerRecursionStep lambda f h k := by
          unfold panjerRecursionStep
          congr 1
          apply Finset.sum_congr rfl
          intro j hj
          have hlt : k - j < k + 1 := Nat.lt_succ_of_le (Nat.sub_le k j)
          rw [ih (k - j) hlt]
        _ = h (k + 1) := (hh.2 k).symm
