-- Prove2me | solution 1 for ActuarialValuation.ipFold_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:56:50.405987+00:00
-- url     : https://prove2.me/submissions/01674e85-bcc4-4fb1-8a71-f99df8553557

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ipPoint
import Definitions.Def_actuarial_ipFold
open ActuarialValuation

theorem solution(f : ℕ → ℝ) (k : ℕ) : ipFold f 0 k=ipPoint k := by
  first
  | (simp [ipPoint, ipFold, ipConvolve]; done)
  | (norm_num [ipPoint, ipFold, ipConvolve]; done)
  | (unfold ipPoint ipFold ipConvolve; positivity)
  | (simp only [ipPoint, ipFold, ipConvolve]; positivity)
  | (unfold ipPoint ipFold ipConvolve; ring)
  | (unfold ipPoint ipFold ipConvolve; simp; done)
  | (unfold ipPoint ipFold ipConvolve; norm_num; done)
  | (simp [ipPoint, ipFold, ipConvolve]; ring)
  | (unfold ipPoint ipFold ipConvolve; split_ifs <;> simp_all <;> linarith)
  | (unfold ipPoint ipFold ipConvolve; nlinarith [sq_nonneg 0])
  | (simp_all [ipPoint, ipFold, ipConvolve]; done)
  | (unfold ipPoint ipFold ipConvolve; simp_all; done)
  | rfl
