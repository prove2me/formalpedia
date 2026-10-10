-- Prove2me | solution 1 for ActuarialValuation.cm1UDDFractionalSurvival_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:25:17.961897+00:00
-- url     : https://prove2.me/submissions/1ffb0560-9de0-4d97-88a5-8544788bafe2

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1UDDFractionalSurvival
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : ℝ) : cm1UDDFractionalSurvival p 1 = p := by
  unfold cm1UDDFractionalSurvival
  ring
