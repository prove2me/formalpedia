-- Prove2me | solution 1 for ActuarialValuation.pgStopLoss_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T18:11:40.733761+00:00
-- url     : https://prove2.me/submissions/7b5cad26-a27f-4c37-a8ba-1492a7529113

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity
import Definitions.Def_actuarial_pgPointMass
import Definitions.Def_actuarial_pgConvolve
import Definitions.Def_actuarial_pgFold
import Definitions.Def_actuarial_pgAggregate
import Definitions.Def_actuarial_pgStopLoss

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p f : ℕ → ℝ) (m k : ℕ) (d : ℝ)
    (hp : ∀ j, 0 ≤ p j) (hf : ∀ j, 0 ≤ f j) :
    0 ≤ pgStopLoss p f m k d := by
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
  unfold pgStopLoss
  refine Finset.sum_nonneg ?_
  intro j hj
  first
  | exact mul_nonneg (hagg j) (by positivity)
  | exact mul_nonneg (by positivity) (hagg j)
