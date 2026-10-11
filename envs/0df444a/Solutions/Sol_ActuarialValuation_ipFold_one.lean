-- Prove2me | solution 1 for ActuarialValuation.ipFold_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:16:07.583193+00:00
-- url     : https://prove2.me/submissions/337aac06-db16-4be1-afdc-845410987354

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ipFold
open ActuarialValuation

theorem solution(f : ℕ → ℝ) (k : ℕ) : ipFold f 1 k=f k := by
  show ipConvolve f ipPoint k = f k
  unfold ipConvolve
  rw [Finset.sum_eq_single k]
  · simp [ipPoint]
  · intro b hb hbk
    rw [Finset.mem_range] at hb
    have : k - b ≠ 0 := by omega
    simp [ipPoint, this]
  · intro hk
    exfalso; apply hk; rw [Finset.mem_range]; omega
