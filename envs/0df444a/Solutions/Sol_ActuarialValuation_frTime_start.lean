-- Prove2me | solution 1 for ActuarialValuation.frTime_start
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T19:53:32.230185+00:00
-- url     : https://prove2.me/submissions/7b2de77d-0999-4d49-95f0-81991194335f

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frTime
open ActuarialValuation

theorem solution(k m : ℕ) : frTime k 0 m = (k:ℝ) := by
  first
  | (simp [frTime]; done)
  | (norm_num [frTime]; done)
  | (unfold frTime; positivity)
  | (simp only [frTime]; positivity)
  | (unfold frTime; ring)
  | (unfold frTime; simp; done)
  | (unfold frTime; norm_num; done)
  | (simp [frTime]; ring)
  | (unfold frTime; split_ifs <;> simp_all <;> linarith)
  | (unfold frTime; nlinarith [sq_nonneg 0])
  | rfl
