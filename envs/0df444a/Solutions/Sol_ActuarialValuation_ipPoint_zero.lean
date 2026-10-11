-- Prove2me | solution 1 for ActuarialValuation.ipPoint_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T19:41:52.467674+00:00
-- url     : https://prove2.me/submissions/da968089-ce32-479c-bb8c-b8bc4c2a88b9

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ipPoint
open ActuarialValuation

theorem solution: ipPoint 0=1 := by
  first
  | (simp [ipPoint]; done)
  | (norm_num [ipPoint]; done)
  | (unfold ipPoint; positivity)
  | (simp only [ipPoint]; positivity)
  | (unfold ipPoint; ring)
  | (unfold ipPoint; simp; done)
  | (unfold ipPoint; norm_num; done)
  | (simp [ipPoint]; ring)
  | (unfold ipPoint; split_ifs <;> simp_all <;> linarith)
  | (unfold ipPoint; nlinarith [sq_nonneg 0])
  | rfl
