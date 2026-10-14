-- Prove2me | solution 1 for ActuarialValuation.frReserve_zero_mortality
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:21:49.18417+00:00
-- url     : https://prove2.me/submissions/ac4dcbc5-31e2-49b7-909c-2ece4a9fe83e

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frFractionalReserve
open ActuarialValuation

theorem solution(assets premium benefit s growth endDiscount : ℝ) : frFractionalReserve assets premium benefit 0 s growth endDiscount = (assets+premium)*growth := by
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
