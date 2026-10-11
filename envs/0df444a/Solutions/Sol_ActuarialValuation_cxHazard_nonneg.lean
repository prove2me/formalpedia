-- Prove2me | solution 1 for ActuarialValuation.cxHazard_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:11:58.585355+00:00
-- url     : https://prove2.me/submissions/4759871f-248e-4ae6-8f06-4bce58070ad3

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_cxHazard
open ActuarialValuation

theorem solution(base beta z : ℝ) (h : 0≤base) : 0≤cxHazard base beta z := by
  unfold cxHazard cxRelativeRisk
  exact mul_nonneg h (Real.exp_pos _).le
