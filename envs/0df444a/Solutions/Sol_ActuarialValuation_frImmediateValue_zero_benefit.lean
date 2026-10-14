-- Prove2me | solution 1 for ActuarialValuation.frImmediateValue_zero_benefit
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T08:47:12.461988+00:00
-- url     : https://prove2.me/submissions/0f1872e1-ba54-4b17-83aa-e0bf0ec54d8b

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frImmediateValue
open ActuarialValuation

theorem solution(discount : ℝ → ℝ) (p q : ℕ → ℝ) (n m : ℕ) : frImmediateValue (fun _ => 0) discount p q n m = 0 := by
  first
  | (simp [frImmediateValue, frImmediateTerm, frTime, frUddSurvival]; done)
  | (norm_num [frImmediateValue, frImmediateTerm, frTime, frUddSurvival]; done)
  | (unfold frImmediateValue frImmediateTerm frTime frUddSurvival; positivity)
  | (simp only [frImmediateValue, frImmediateTerm, frTime, frUddSurvival]; positivity)
  | (unfold frImmediateValue frImmediateTerm frTime frUddSurvival; ring)
  | (unfold frImmediateValue frImmediateTerm frTime frUddSurvival; simp; done)
  | (unfold frImmediateValue frImmediateTerm frTime frUddSurvival; norm_num; done)
  | (simp [frImmediateValue, frImmediateTerm, frTime, frUddSurvival]; ring)
  | (unfold frImmediateValue frImmediateTerm frTime frUddSurvival; split_ifs <;> simp_all <;> linarith)
  | (unfold frImmediateValue frImmediateTerm frTime frUddSurvival; nlinarith [sq_nonneg 0])
  | (simp_all [frImmediateValue, frImmediateTerm, frTime, frUddSurvival]; done)
  | (unfold frImmediateValue frImmediateTerm frTime frUddSurvival; simp_all; done)
  | rfl
