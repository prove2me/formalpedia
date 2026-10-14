-- Prove2me | solution 1 for ActuarialValuation.gmGammaDeviance_at_fit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:29:14.478981+00:00
-- url     : https://prove2.me/submissions/91a75a55-3204-44cb-910d-4ed9dcea36b0

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_gmGammaDeviance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (observed : ℝ) (h : observed ≠ 0) :
    gmGammaDeviance observed observed = 0 := by
  simp [gmGammaDeviance, h]
