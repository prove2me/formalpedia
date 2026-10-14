-- Prove2me | solution 1 for ActuarialValuation.frDue_annual_frequency
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T08:49:30.755579+00:00
-- url     : https://prove2.me/submissions/83be7182-a1a4-4d0c-8488-aa8ee41cb078

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frDueValue
import Definitions.Def_actuarial_frAnnualDueValue
open ActuarialValuation

theorem solution(c : ℕ → ℝ) (discount : ℝ → ℝ) (p q : ℕ → ℝ) (n : ℕ) : frDueValue c discount p q n 1 = frAnnualDueValue c discount p n := by
  first
  | (simp [frDueValue, frDueTerm, frTime, frUddSurvival, frAnnualDueValue]; done)
  | (norm_num [frDueValue, frDueTerm, frTime, frUddSurvival, frAnnualDueValue]; done)
  | (unfold frDueValue frDueTerm frTime frUddSurvival frAnnualDueValue; positivity)
  | (simp only [frDueValue, frDueTerm, frTime, frUddSurvival, frAnnualDueValue]; positivity)
  | (unfold frDueValue frDueTerm frTime frUddSurvival frAnnualDueValue; ring)
  | (unfold frDueValue frDueTerm frTime frUddSurvival frAnnualDueValue; simp; done)
  | (unfold frDueValue frDueTerm frTime frUddSurvival frAnnualDueValue; norm_num; done)
  | (simp [frDueValue, frDueTerm, frTime, frUddSurvival, frAnnualDueValue]; ring)
  | (unfold frDueValue frDueTerm frTime frUddSurvival frAnnualDueValue; split_ifs <;> simp_all <;> linarith)
  | (unfold frDueValue frDueTerm frTime frUddSurvival frAnnualDueValue; nlinarith [sq_nonneg 0])
  | (simp_all [frDueValue, frDueTerm, frTime, frUddSurvival, frAnnualDueValue]; done)
  | (unfold frDueValue frDueTerm frTime frUddSurvival frAnnualDueValue; simp_all; done)
  | rfl
