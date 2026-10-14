-- Prove2me | solution 1 for ActuarialValuation.pen9ActiveProbability_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:53:25.467848+00:00
-- url     : https://prove2.me/submissions/e60f9878-3aca-425e-8c88-c6476d37b455

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9ExitMass
import Definitions.Def_actuarial_pen9ActiveProbability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (w d i r : ℝ) (hw : 0 ≤ w) (hd : 0 ≤ d) (hi : 0 ≤ i) (hr : 0 ≤ r) (h : pen9ExitMass w d i r ≤ 1) : 0 ≤ pen9ActiveProbability w d i r ∧ pen9ActiveProbability w d i r ≤ 1 := by
  dsimp only [pen9ActiveProbability, pen9ExitMass] at *
  constructor <;> linarith
