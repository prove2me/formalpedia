-- Prove2me | solution 1 for ActuarialValuation.frReserve_annual
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:20:59.044053+00:00
-- url     : https://prove2.me/submissions/b9bbd7da-f323-4d3f-8c85-187175c3917d

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frFractionalReserve
import Definitions.Def_actuarial_frAnnualReserve
open ActuarialValuation

theorem solution(assets premium benefit q growth : ℝ) : frFractionalReserve assets premium benefit q 1 growth 1 = frAnnualReserve assets premium benefit q growth := by
  first
  | (simp [frFractionalReserve, frUddSurvival, frAnnualReserve]; done)
  | (norm_num [frFractionalReserve, frUddSurvival, frAnnualReserve]; done)
  | (unfold frFractionalReserve frUddSurvival frAnnualReserve; positivity)
  | (simp only [frFractionalReserve, frUddSurvival, frAnnualReserve]; positivity)
  | (unfold frFractionalReserve frUddSurvival frAnnualReserve; ring)
  | (unfold frFractionalReserve frUddSurvival frAnnualReserve; simp; done)
  | (unfold frFractionalReserve frUddSurvival frAnnualReserve; norm_num; done)
  | (simp [frFractionalReserve, frUddSurvival, frAnnualReserve]; ring)
  | (unfold frFractionalReserve frUddSurvival frAnnualReserve; split_ifs <;> simp_all <;> linarith)
  | (unfold frFractionalReserve frUddSurvival frAnnualReserve; nlinarith [sq_nonneg 0])
  | (simp_all [frFractionalReserve, frUddSurvival, frAnnualReserve]; done)
  | (unfold frFractionalReserve frUddSurvival frAnnualReserve; simp_all; done)
  | rfl
