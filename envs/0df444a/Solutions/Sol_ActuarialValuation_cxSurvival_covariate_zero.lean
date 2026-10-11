-- Prove2me | solution 1 for ActuarialValuation.cxSurvival_covariate_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:39:33.435648+00:00
-- url     : https://prove2.me/submissions/ab03fd98-d02b-40ca-a28c-761f24c19e6b

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_cxSurvival
open ActuarialValuation

theorem solution(H beta : ℝ) : cxSurvival H beta 0=Real.exp (-H) := by
  simp [cxSurvival, cxRelativeRisk]
