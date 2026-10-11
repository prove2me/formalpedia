-- Prove2me | solution 1 for ActuarialValuation.kmSurvival_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:44:30.224604+00:00
-- url     : https://prove2.me/submissions/f918cb50-c117-41ed-b053-bb858047b3b2

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmSurvival
open ActuarialValuation

theorem solution(r d : ℕ → ℝ) : kmSurvival r d 0 = 1 := by
  first
  | (simp [kmSurvival, kmSurvivalFactor, kmDeathHazard]; done)
  | (norm_num [kmSurvival, kmSurvivalFactor, kmDeathHazard]; done)
  | (unfold kmSurvival kmSurvivalFactor kmDeathHazard; positivity)
  | (simp only [kmSurvival, kmSurvivalFactor, kmDeathHazard]; positivity)
  | (unfold kmSurvival kmSurvivalFactor kmDeathHazard; ring)
  | (unfold kmSurvival kmSurvivalFactor kmDeathHazard; simp; done)
  | (unfold kmSurvival kmSurvivalFactor kmDeathHazard; norm_num; done)
  | (simp [kmSurvival, kmSurvivalFactor, kmDeathHazard]; ring)
  | (unfold kmSurvival kmSurvivalFactor kmDeathHazard; split_ifs <;> simp_all <;> linarith)
  | (unfold kmSurvival kmSurvivalFactor kmDeathHazard; nlinarith [sq_nonneg 0])
  | (simp_all [kmSurvival, kmSurvivalFactor, kmDeathHazard]; done)
  | (unfold kmSurvival kmSurvivalFactor kmDeathHazard; simp_all; done)
  | rfl
