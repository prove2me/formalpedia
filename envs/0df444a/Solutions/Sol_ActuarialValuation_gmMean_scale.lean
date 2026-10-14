-- Prove2me | solution 1 for ActuarialValuation.gmMean_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:29:26.142993+00:00
-- url     : https://prove2.me/submissions/169c11ef-babc-4d9d-9841-955000a184da

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_gmMean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (exposure factor eta : ℝ) :
    gmMean (factor * exposure) eta = factor * gmMean exposure eta := by
  simp only [gmMean, mul_assoc]
