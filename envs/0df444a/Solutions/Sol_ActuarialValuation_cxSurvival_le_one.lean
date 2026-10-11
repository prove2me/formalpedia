-- Prove2me | solution 1 for ActuarialValuation.cxSurvival_le_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T09:07:07.603522+00:00
-- url     : https://prove2.me/submissions/7709fbcf-662c-4a87-8cbc-554d8270003d

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_cxSurvival
open ActuarialValuation

theorem solution(H beta z : ℝ) (hH : 0≤H) : cxSurvival H beta z≤1 := by
  unfold cxSurvival
  rw [show (1:ℝ) = Real.exp 0 from Real.exp_zero.symm]
  apply Real.exp_le_exp.mpr
  have := Real.exp_pos (beta * z)
  unfold cxRelativeRisk
  nlinarith
