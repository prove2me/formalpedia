-- Prove2me | solution 1 for ActuarialValuation.panjerRecursionStep_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:18:49.612227+00:00
-- url     : https://prove2.me/submissions/a7aa2fc4-8167-41f5-9705-6656ac2ad1af

import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerRecursionStep

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (lambda : ℝ) (f g : ℕ → ℝ) (k : ℕ) (hl : 0 ≤ lambda) (hf : ∀ j, 0 ≤ f j) (hg : ∀ j, 0 ≤ g j) : 0 ≤ panjerRecursionStep lambda f g k := by
  unfold panjerRecursionStep
  apply mul_nonneg
  · apply div_nonneg hl
    positivity
  · apply Finset.sum_nonneg
    intro j hj
    unfold panjerWeightedSeverity
    exact mul_nonneg (mul_nonneg (by positivity) (hf (j + 1))) (hg (k - j))
