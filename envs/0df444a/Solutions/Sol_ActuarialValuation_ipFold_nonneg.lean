-- Prove2me | solution 1 for ActuarialValuation.ipFold_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:13:27.662919+00:00
-- url     : https://prove2.me/submissions/89f04286-3761-4e4c-a5ba-0272f55402a6

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ipFold
open ActuarialValuation

theorem solution(f : ℕ → ℝ) (n k : ℕ) (hf : ∀ j, 0≤f j) : 0≤ ipFold f n k := by
  induction n generalizing k with
  | zero =>
    show 0 ≤ ipPoint k
    unfold ipPoint
    split_ifs <;> norm_num
  | succ n ih =>
    show 0 ≤ ipConvolve f (ipFold f n) k
    unfold ipConvolve
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (hf j) (ih _))
