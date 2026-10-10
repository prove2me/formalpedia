-- Prove2me | solution 1 for ActuarialValuation.cm1UDDFractionalSurvival_affine
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:18:10.245556+00:00
-- url     : https://prove2.me/submissions/e471fba5-8b20-4c89-b846-e6a0089cee87

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1UDDFractionalSurvival
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p s t : ℝ) : cm1UDDFractionalSurvival p (s+t) = cm1UDDFractionalSurvival p s + cm1UDDFractionalSurvival p t - 1 := by
  unfold cm1UDDFractionalSurvival
  ring
