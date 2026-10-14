-- Prove2me | solution 1 for ActuarialValuation.ipTail_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:49:36.162242+00:00
-- url     : https://prove2.me/submissions/c2099758-7cb4-4b55-8e11-e8d29642613c

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_actuarial_ipTail

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p f : ℕ → ℝ) (k : ℕ)
    (hp : ∀ n, 0 ≤ p n) (hf : ∀ n, 0 ≤ f n) :
    ipTail p f (k+1) ≤ ipTail p f k := by
  have hfold : ∀ n j, 0 ≤ ipFold f n j := by
    intro n
    induction n with
    | zero =>
      intro j
      show 0 ≤ ipPoint j
      unfold ipPoint
      split_ifs <;> norm_num
    | succ n ih =>
      intro j
      show 0 ≤ ipConvolve f (ipFold f n) j
      unfold ipConvolve
      exact Finset.sum_nonneg (fun i _ => mul_nonneg (hf i) (ih _))
  have hmass : 0 ≤ ipCompound p f (k+1) := by
    unfold ipCompound
    exact tsum_nonneg (fun n => mul_nonneg (hp n) (hfold n (k+1)))
  have hcdf : ipCDF p f (k+1) =
      ipCDF p f k + ipCompound p f (k+1) := by
    simp [ipCDF, Finset.sum_range_succ]
  change 1 - ipCDF p f (k+1) ≤ 1 - ipCDF p f k
  rw [hcdf]
  linarith
