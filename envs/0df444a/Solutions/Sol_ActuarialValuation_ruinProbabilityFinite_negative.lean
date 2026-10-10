-- Prove2me | solution 1 for ActuarialValuation.ruinProbabilityFinite_negative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:49:27.341326+00:00
-- url     : https://prove2.me/submissions/80382bc3-dcc5-40e7-94e1-e66189da9262

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
  (w : ℕ → ℝ) (B c n : ℕ) (u : ℤ) (hu : u < 0) :
  ruinProbabilityFinite w B c n u = 1 := by
  induction n with
  | zero => simp [ruinProbabilityFinite, hu]
  | succ n ih => simp [ruinProbabilityFinite, hu]
