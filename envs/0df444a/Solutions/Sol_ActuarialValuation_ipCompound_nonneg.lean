-- Prove2me | solution 1 for ActuarialValuation.ipCompound_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:10:26.452049+00:00
-- url     : https://prove2.me/submissions/a05c0369-8da8-449e-8531-83500483badc

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.NormNum
import Definitions.Def_actuarial_ipCompound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p f : ℕ → ℝ) (k : ℕ)
    (hp : ∀ j, 0 ≤ p j) (hf : ∀ j, 0 ≤ f j) :
    0 ≤ ipCompound p f k := by
  have hfold : ∀ n k, 0 ≤ ipFold f n k := by
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
  unfold ipCompound
  exact tsum_nonneg (fun n => mul_nonneg (hp n) (hfold n k))
