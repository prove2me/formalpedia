-- Prove2me | solution 1 for ActuarialValuation.frUdd_death
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T12:50:03.281536+00:00
-- url     : https://prove2.me/submissions/e65047e8-c258-4fba-ab55-52f2dd8624a8

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frUddSurvival
open ActuarialValuation

theorem solution(q s : ℝ) : 1 - frUddSurvival q s = s*q := by
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
  | (simp_all [frUddSurvival]; done)
  | (unfold frUddSurvival; simp_all; done)
  | rfl
