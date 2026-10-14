-- Prove2me | solution 1 for ActuarialValuation.gmLogMean_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:23:19.346556+00:00
-- url     : https://prove2.me/submissions/032443a1-1e1f-41b5-9a55-35c1acc23b4f

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_gmMean
import Definitions.Def_actuarial_gmLogMean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (exposure eta : ℝ) (hE : 0 < exposure) :
    Real.log (gmMean exposure eta) = gmLogMean exposure eta := by
  simp only [gmMean, gmLogMean]
  rw [Real.log_mul (ne_of_gt hE) (Real.exp_ne_zero eta), Real.log_exp]
