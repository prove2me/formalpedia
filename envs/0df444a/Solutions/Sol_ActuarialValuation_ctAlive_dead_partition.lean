-- Prove2me | solution 1 for ActuarialValuation.ctAlive_dead_partition
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T14:33:50.804534+00:00
-- url     : https://prove2.me/submissions/d5e6185a-1931-4df4-9995-52cdce408971

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctAlive
import Definitions.Def_actuarial_ctDead
open ActuarialValuation

theorem solution(mu t : ℝ) : ctAlive mu t+ctDead mu t=1 := by
  first
  | (simp [ctAlive, ctDead]; done)
  | (norm_num [ctAlive, ctDead]; done)
  | (unfold ctAlive ctDead; positivity)
  | (simp only [ctAlive, ctDead]; positivity)
  | (unfold ctAlive ctDead; ring)
  | (unfold ctAlive ctDead; simp; done)
  | (unfold ctAlive ctDead; norm_num; done)
  | (simp [ctAlive, ctDead]; ring)
  | (unfold ctAlive ctDead; split_ifs <;> simp_all <;> linarith)
  | (unfold ctAlive ctDead; nlinarith [sq_nonneg 0])
  | (simp_all [ctAlive, ctDead]; done)
  | (unfold ctAlive ctDead; simp_all; done)
  | rfl
