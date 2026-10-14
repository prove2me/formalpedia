-- Prove2me | solution 1 for ActuarialValuation.frDueValue_zero_benefit
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T08:46:22.043982+00:00
-- url     : https://prove2.me/submissions/8547a494-0fba-450e-b2c4-62caa2d12f13

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frDueValue
open ActuarialValuation

theorem solution(discount : ℝ → ℝ) (p q : ℕ → ℝ) (n m : ℕ) : frDueValue (fun _ => 0) discount p q n m = 0 := by
  first
  | (simp [frDueValue, frDueTerm, frTime, frUddSurvival]; done)
  | (norm_num [frDueValue, frDueTerm, frTime, frUddSurvival]; done)
  | (unfold frDueValue frDueTerm frTime frUddSurvival; positivity)
  | (simp only [frDueValue, frDueTerm, frTime, frUddSurvival]; positivity)
  | (unfold frDueValue frDueTerm frTime frUddSurvival; ring)
  | (unfold frDueValue frDueTerm frTime frUddSurvival; simp; done)
  | (unfold frDueValue frDueTerm frTime frUddSurvival; norm_num; done)
  | (simp [frDueValue, frDueTerm, frTime, frUddSurvival]; ring)
  | (unfold frDueValue frDueTerm frTime frUddSurvival; split_ifs <;> simp_all <;> linarith)
  | (unfold frDueValue frDueTerm frTime frUddSurvival; nlinarith [sq_nonneg 0])
  | (simp_all [frDueValue, frDueTerm, frTime, frUddSurvival]; done)
  | (unfold frDueValue frDueTerm frTime frUddSurvival; simp_all; done)
  | rfl
