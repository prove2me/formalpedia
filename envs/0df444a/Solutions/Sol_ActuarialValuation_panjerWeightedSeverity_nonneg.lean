-- Prove2me | solution 1 for ActuarialValuation.panjerWeightedSeverity_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:12:40.789411+00:00
-- url     : https://prove2.me/submissions/c1debff6-81e0-49f9-ad72-7be34470d248

import Mathlib.Tactic.Positivity
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerWeightedSeverity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (f : ℕ → ℝ) (k : ℕ) (h : 0 ≤ f k) : 0 ≤ panjerWeightedSeverity f k := by
  unfold panjerWeightedSeverity
  exact mul_nonneg (by positivity) h
