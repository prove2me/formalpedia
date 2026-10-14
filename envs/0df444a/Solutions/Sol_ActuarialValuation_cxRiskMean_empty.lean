-- Prove2me | solution 1 for ActuarialValuation.cxRiskMean_empty
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:30:06.812025+00:00
-- url     : https://prove2.me/submissions/cba70282-0e4a-4cbe-844a-8a7126a77da0

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_cxRiskMean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (beta : ℝ) (z : Fin n → ℝ) : cxRiskMean beta ∅ z=0 := by
  simp [cxRiskMean, cxRiskWeighted, cxRiskDenom]
