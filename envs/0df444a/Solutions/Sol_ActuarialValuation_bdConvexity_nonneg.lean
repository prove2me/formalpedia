-- Prove2me | solution 1 for ActuarialValuation.bdConvexity_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:53:02.866923+00:00
-- url     : https://prove2.me/submissions/4840ee28-aae2-479d-8d30-ab8abb2f9a6c

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdConvexityNumerator

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (D c : ℕ → ℝ) (n : ℕ) (hD : ∀ k∈Finset.range n, 0≤D (k+1)) (hc : ∀ k∈Finset.range n, 0≤c k) : 0≤bdConvexityNumerator D c n := by
  unfold bdConvexityNumerator
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (hc k hk)) (hD k hk)
