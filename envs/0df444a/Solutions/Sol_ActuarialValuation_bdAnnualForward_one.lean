-- Prove2me | solution 1 for ActuarialValuation.bdAnnualForward_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:38:16.138986+00:00
-- url     : https://prove2.me/submissions/3f3410a8-98ed-4a35-97fd-70d5ffb4ff38

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdAnnualForward
import Definitions.Def_actuarial_bdForwardGross
open ActuarialValuation

theorem solution(D : ℕ → ℝ) (t : ℕ) : bdAnnualForward D t = bdForwardGross D t (t+1)-1 := by
  first
  | (simp [bdAnnualForward, bdSimpleForward, bdForwardGross]; done)
  | (norm_num [bdAnnualForward, bdSimpleForward, bdForwardGross]; done)
  | (unfold bdAnnualForward bdSimpleForward bdForwardGross; positivity)
  | (simp only [bdAnnualForward, bdSimpleForward, bdForwardGross]; positivity)
  | (unfold bdAnnualForward bdSimpleForward bdForwardGross; ring)
  | (unfold bdAnnualForward bdSimpleForward bdForwardGross; simp; done)
  | (unfold bdAnnualForward bdSimpleForward bdForwardGross; norm_num; done)
  | (simp [bdAnnualForward, bdSimpleForward, bdForwardGross]; ring)
  | (unfold bdAnnualForward bdSimpleForward bdForwardGross; split_ifs <;> simp_all <;> linarith)
  | (unfold bdAnnualForward bdSimpleForward bdForwardGross; nlinarith [sq_nonneg 0])
  | (simp_all [bdAnnualForward, bdSimpleForward, bdForwardGross]; done)
  | (unfold bdAnnualForward bdSimpleForward bdForwardGross; simp_all; done)
  | rfl
