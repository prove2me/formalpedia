-- Prove2me | solution 1 for ActuarialValuation.gammaPoissonPosteriorShape_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:39:56.980627+00:00
-- url     : https://prove2.me/submissions/136ee139-523a-45d4-a0f1-38068dff4547

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_gammaPoissonPosteriorShape

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a : ℝ) :
  gammaPoissonPosteriorShape a 0 = a := by
  simp [gammaPoissonPosteriorShape]
