-- Prove2me | solution 1 for ActuarialValuation.frReserve_start
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:20:57.747464+00:00
-- url     : https://prove2.me/submissions/860b9031-872b-425c-8466-f458579d47b7

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frFractionalReserve
open ActuarialValuation

theorem solution(assets premium benefit q : ℝ) (endDiscount : ℝ) : frFractionalReserve assets premium benefit q 0 1 endDiscount = assets+premium := by
  first
  | (simp [frFractionalReserve, frUddSurvival]; done)
  | (norm_num [frFractionalReserve, frUddSurvival]; done)
  | (unfold frFractionalReserve frUddSurvival; positivity)
  | (simp only [frFractionalReserve, frUddSurvival]; positivity)
  | (unfold frFractionalReserve frUddSurvival; ring)
  | (unfold frFractionalReserve frUddSurvival; simp; done)
  | (unfold frFractionalReserve frUddSurvival; norm_num; done)
  | (simp [frFractionalReserve, frUddSurvival]; ring)
  | (unfold frFractionalReserve frUddSurvival; split_ifs <;> simp_all <;> linarith)
  | (unfold frFractionalReserve frUddSurvival; nlinarith [sq_nonneg 0])
  | (simp_all [frFractionalReserve, frUddSurvival]; done)
  | (unfold frFractionalReserve frUddSurvival; simp_all; done)
  | rfl
