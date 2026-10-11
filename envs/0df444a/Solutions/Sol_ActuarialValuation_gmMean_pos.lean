-- Prove2me | solution 1 for ActuarialValuation.gmMean_pos
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:14:43.788555+00:00
-- url     : https://prove2.me/submissions/2e16aa60-7c01-4efd-becb-c5a1a7871c5c

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_gmMean
open ActuarialValuation

theorem solution(exposure eta : ℝ) (hE : 0 < exposure) : 0 < gmMean exposure eta := by
  unfold gmMean
  exact mul_pos hE (Real.exp_pos _)
