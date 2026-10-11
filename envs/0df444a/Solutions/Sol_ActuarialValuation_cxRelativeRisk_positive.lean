-- Prove2me | solution 1 for ActuarialValuation.cxRelativeRisk_positive
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T07:20:36.223588+00:00
-- url     : https://prove2.me/submissions/d179b7fc-c345-43c3-8ca8-f87b742fbb13

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_cxRelativeRisk
open ActuarialValuation

theorem solution(beta z : ℝ) : 0 < cxRelativeRisk beta z := by
  unfold cxRelativeRisk
  exact Real.exp_pos _
