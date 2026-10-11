-- Prove2me | solution 1 for ActuarialValuation.pgPointMass_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T19:42:01.267897+00:00
-- url     : https://prove2.me/submissions/48ee8a86-3b80-427f-9386-0135f8a191b9

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgPointMass
open ActuarialValuation

theorem solution: pgPointMass 0=1 := by
  first
  | (simp [pgPointMass]; done)
  | (norm_num [pgPointMass]; done)
  | (unfold pgPointMass; positivity)
  | (simp only [pgPointMass]; positivity)
  | (unfold pgPointMass; ring)
  | (unfold pgPointMass; simp; done)
  | (unfold pgPointMass; norm_num; done)
  | (simp [pgPointMass]; ring)
  | (unfold pgPointMass; split_ifs <;> simp_all <;> linarith)
  | (unfold pgPointMass; nlinarith [sq_nonneg 0])
  | rfl
