-- Prove2me | solution 1 for ActuarialValuation.frImmediateValue_empty
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T08:47:07.376+00:00
-- url     : https://prove2.me/submissions/7da71f8c-967a-4e00-9a05-504e4e6187bd

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frImmediateValue
open ActuarialValuation

theorem solution(c : ℕ → ℝ) (discount : ℝ → ℝ) (p q : ℕ → ℝ) (m : ℕ) : frImmediateValue c discount p q 0 m = 0 := by
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
