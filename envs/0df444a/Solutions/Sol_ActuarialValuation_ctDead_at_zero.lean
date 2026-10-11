-- Prove2me | solution 1 for ActuarialValuation.ctDead_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T19:50:15.964714+00:00
-- url     : https://prove2.me/submissions/59623c63-cf36-465e-b60a-354d4f057493

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctDead
open ActuarialValuation

theorem solution(mu : ℝ) : ctDead mu 0 = 0 := by
  first
  | (simp [ctDead, ctAlive]; done)
  | (norm_num [ctDead, ctAlive]; done)
  | (unfold ctDead ctAlive; positivity)
  | (simp only [ctDead, ctAlive]; positivity)
  | (unfold ctDead ctAlive; ring)
  | (unfold ctDead ctAlive; simp; done)
  | (unfold ctDead ctAlive; norm_num; done)
  | (simp [ctDead, ctAlive]; ring)
  | (unfold ctDead ctAlive; split_ifs <;> simp_all <;> linarith)
  | (unfold ctDead ctAlive; nlinarith [sq_nonneg 0])
  | rfl
