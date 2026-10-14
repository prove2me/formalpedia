-- Prove2me | solution 1 for ActuarialValuation.pgAggregate_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T18:07:10.646001+00:00
-- url     : https://prove2.me/submissions/a9de5380-ea84-426b-9e1d-26d552a04e74

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_actuarial_pgAggregate
import Definitions.Def_actuarial_pgFold
import Definitions.Def_actuarial_pgConvolve
import Definitions.Def_actuarial_pgPointMass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p f : ℕ → ℝ) (m k : ℕ)
    (hp : ∀ j, 0 ≤ p j) (hf : ∀ j, 0 ≤ f j) :
    0 ≤ pgAggregate p f m k := by
  have hfold (n : ℕ) : ∀ x, 0 ≤ pgFold f n x := by
    induction n with
    | zero =>
      intro x
      by_cases hx : x = 0
      · simp [pgFold, pgPointMass, hx]
      · simp [pgFold, pgPointMass, hx]
    | succ n ih =>
      intro x
      change 0 ≤ pgConvolve f (pgFold f n) x
      unfold pgConvolve
      refine Finset.sum_nonneg ?_
      intro j hj
      exact mul_nonneg (hf j) (ih (x - j))
  unfold pgAggregate
  refine Finset.sum_nonneg ?_
  intro j hj
  exact mul_nonneg (hp j) (hfold j k)
