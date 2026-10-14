-- Prove2me | solution 1 for ActuarialValuation.bdDurationNumerator_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:58:19.821494+00:00
-- url     : https://prove2.me/submissions/b30a8123-0fa7-4d52-986c-9ad6f2bd3091

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdDurationNumerator

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (D c : ℕ → ℝ) (n : ℕ) (hD : ∀ k∈Finset.range n, 0≤D (k+1)) (hc : ∀ k∈Finset.range n, 0≤c k) : 0≤bdDurationNumerator D c n := by
  unfold bdDurationNumerator
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg (mul_nonneg (by positivity) (hc k hk)) (hD k hk)
