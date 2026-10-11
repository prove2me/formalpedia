-- Prove2me | solution 1 for ActuarialValuation.cxSurvival_start
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:44:39.291374+00:00
-- url     : https://prove2.me/submissions/14c648c0-c766-4c36-b28d-a67aab98cf99

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_cxSurvival
open ActuarialValuation

theorem solution(beta z : ℝ) : cxSurvival 0 beta z=1 := by
  first
  | (simp [cxSurvival, cxRelativeRisk]; done)
  | (norm_num [cxSurvival, cxRelativeRisk]; done)
  | (unfold cxSurvival cxRelativeRisk; positivity)
  | (simp only [cxSurvival, cxRelativeRisk]; positivity)
  | (unfold cxSurvival cxRelativeRisk; ring)
  | (unfold cxSurvival cxRelativeRisk; simp; done)
  | (unfold cxSurvival cxRelativeRisk; norm_num; done)
  | (simp [cxSurvival, cxRelativeRisk]; ring)
  | (unfold cxSurvival cxRelativeRisk; split_ifs <;> simp_all <;> linarith)
  | (unfold cxSurvival cxRelativeRisk; nlinarith [sq_nonneg 0])
  | (simp_all [cxSurvival, cxRelativeRisk]; done)
  | (unfold cxSurvival cxRelativeRisk; simp_all; done)
  | rfl
