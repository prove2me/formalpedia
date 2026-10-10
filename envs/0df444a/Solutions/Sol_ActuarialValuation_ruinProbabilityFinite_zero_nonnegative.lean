-- Prove2me | solution 1 for ActuarialValuation.ruinProbabilityFinite_zero_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:56:35.534296+00:00
-- url     : https://prove2.me/submissions/4c1c2122-55f7-4ff2-9d57-d4f45b332357

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ruinProbabilityFinite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (w : ℕ → ℝ) (B c : ℕ) (u : ℤ) (hu : 0 ≤ u) :
  ruinProbabilityFinite w B c 0 u = 0 := by
  simp [ruinProbabilityFinite, not_lt_of_ge hu]
