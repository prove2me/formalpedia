-- Prove2me | solution 1 for ActuarialValuation.ipPoint_positive
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:11:38.760739+00:00
-- url     : https://prove2.me/submissions/5ca44e4e-057e-4d79-85f0-f8f81f0aeb70

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ipPoint
open ActuarialValuation

theorem solution(k : ℕ) (h : 0<k) : ipPoint k=0 := by
  unfold ipPoint
  rw [if_neg (Nat.pos_iff_ne_zero.mp h)]
