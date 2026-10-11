-- Prove2me | solution 1 for ActuarialValuation.cxSurvival_positive
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T06:15:49.660797+00:00
-- url     : https://prove2.me/submissions/f3cff8f9-873c-49c4-aad2-2160418091a3

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_cxSurvival
open ActuarialValuation

theorem solution(H beta z : ℝ) : 0 < cxSurvival H beta z := by
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
