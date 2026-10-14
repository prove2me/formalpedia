-- Prove2me | solution 1 for ActuarialValuation.gmMean_add_exposure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:30:39.806988+00:00
-- url     : https://prove2.me/submissions/938d0658-548d-4890-a48b-9ef3a09bb691

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_gmMean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (ex1 ex2 eta : ℝ) :
    gmMean (ex1 + ex2) eta = gmMean ex1 eta + gmMean ex2 eta := by
  simp only [gmMean, add_mul]
