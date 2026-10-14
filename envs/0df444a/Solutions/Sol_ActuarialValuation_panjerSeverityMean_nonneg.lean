-- Prove2me | solution 1 for ActuarialValuation.panjerSeverityMean_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:12:15.777529+00:00
-- url     : https://prove2.me/submissions/567b1294-bfd2-443c-85af-f45991867311

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerSeverityMean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (f : ℕ → ℝ) (n : ℕ) (h : ∀ k ∈ Finset.range (n+1), 0 ≤ f k) : 0 ≤ panjerSeverityMean f n := by
  unfold panjerSeverityMean
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (by positivity) (h j hj)
