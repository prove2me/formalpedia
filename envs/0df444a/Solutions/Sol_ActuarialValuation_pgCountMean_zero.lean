-- Prove2me | solution 1 for ActuarialValuation.pgCountMean_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:11:41.674991+00:00
-- url     : https://prove2.me/submissions/3a178bd1-e357-48f2-81a3-feefde615925

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgCountMean
open ActuarialValuation

theorem solution(p : ℕ → ℝ) : pgCountMean p 0=0 := by
  first
  | (simp [pgCountMean]; done)
  | (norm_num [pgCountMean]; done)
  | (unfold pgCountMean; positivity)
  | (simp only [pgCountMean]; positivity)
  | (unfold pgCountMean; ring)
  | (unfold pgCountMean; simp; done)
  | (unfold pgCountMean; norm_num; done)
  | (simp [pgCountMean]; ring)
  | (unfold pgCountMean; split_ifs <;> simp_all <;> linarith)
  | (unfold pgCountMean; nlinarith [sq_nonneg 0])
  | (simp_all [pgCountMean]; done)
  | (unfold pgCountMean; simp_all; done)
  | rfl
