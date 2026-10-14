-- Prove2me | solution 1 for ActuarialValuation.frUdd_split
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T07:12:30.580516+00:00
-- url     : https://prove2.me/submissions/7063fec9-057d-45bc-b0ba-743da0a63d8f

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frUddSurvival
open ActuarialValuation

theorem solution(q s t : ℝ) : frUddSurvival q (s+t) = frUddSurvival q s - t*q := by
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
