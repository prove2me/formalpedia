-- Prove2me | solution 1 for ActuarialValuation.ipConvolve_right
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:41:17.255489+00:00
-- url     : https://prove2.me/submissions/961c1c7f-2f80-4b56-a200-8922d280bf87

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ipPoint
import Definitions.Def_actuarial_ipConvolve

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (f : ℕ → ℝ) (k : ℕ) : ipConvolve f ipPoint k=f k := by
  unfold ipConvolve
  calc
    (∑ j ∈ Finset.range (k+1), f j * ipPoint (k-j)) = f k * ipPoint (k-k) := by
      apply Finset.sum_eq_single k
      · intro j hj hne
        have hle : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have hlt : j < k := lt_of_le_of_ne hle hne
        have hsub : k - j ≠ 0 := Nat.sub_ne_zero_iff_lt.mpr hlt
        simp [ipPoint, hsub]
      · simp
    _ = f k := by simp [ipPoint]
