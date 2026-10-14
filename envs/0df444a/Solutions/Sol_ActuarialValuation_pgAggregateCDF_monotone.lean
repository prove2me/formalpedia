-- Prove2me | solution 1 for ActuarialValuation.pgAggregateCDF_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:05:24.644981+00:00
-- url     : https://prove2.me/submissions/f6593ac3-221b-4cbf-9cc6-251c6375627d

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_actuarial_pgPointMass
import Definitions.Def_actuarial_pgConvolve
import Definitions.Def_actuarial_pgFold
import Definitions.Def_actuarial_pgAggregate
import Definitions.Def_actuarial_pgAggregateCDF

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p f : ℕ → ℝ) (m k : ℕ)
    (hp : ∀ j, 0 ≤ p j) (hf : ∀ j, 0 ≤ f j) :
    pgAggregateCDF p f m k ≤ pgAggregateCDF p f m (k+1) := by
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
  have hagg (x : ℕ) : 0 ≤ pgAggregate p f m x := by
    unfold pgAggregate
    refine Finset.sum_nonneg ?_
    intro j hj
    exact mul_nonneg (hp j) (hfold j x)
  simp only [pgAggregateCDF, Finset.sum_range_succ]
  exact le_add_of_nonneg_right (hagg (k+1))
