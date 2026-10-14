-- Prove2me | solution 1 for ActuarialValuation.panjerSeverityMass_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:07:53.913839+00:00
-- url     : https://prove2.me/submissions/a5d19c52-c7d1-4da3-8695-d6c123ddcfb3

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerSeverityMass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (f : ℕ → ℝ) (n : ℕ) (h : ∀ k ∈ Finset.range (n+1), 0 ≤ f k) : 0 ≤ panjerSeverityMass f n := by
  unfold panjerSeverityMass
  apply Finset.sum_nonneg
  intro k hk
  exact h k hk
