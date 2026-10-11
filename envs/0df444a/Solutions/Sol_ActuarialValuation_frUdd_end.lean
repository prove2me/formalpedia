-- Prove2me | solution 1 for ActuarialValuation.frUdd_end
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T19:50:24.957788+00:00
-- url     : https://prove2.me/submissions/ad53663f-37b8-4dde-87bc-1e66d77d69b0

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frUddSurvival
open ActuarialValuation

theorem solution(q : ℝ) : frUddSurvival q 1 = 1-q := by
  first
  | (simp [frUddSurvival]; done)
  | (norm_num [frUddSurvival]; done)
  | (unfold frUddSurvival; positivity)
  | (simp only [frUddSurvival]; positivity)
  | (unfold frUddSurvival; ring)
  | (unfold frUddSurvival; simp; done)
  | (unfold frUddSurvival; norm_num; done)
  | (simp [frUddSurvival]; ring)
  | (unfold frUddSurvival; split_ifs <;> simp_all <;> linarith)
  | (unfold frUddSurvival; nlinarith [sq_nonneg 0])
  | rfl
