-- Prove2me | solution 1 for ActuarialValuation.aggregateVsPerClaim_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:08:29.003535+00:00
-- url     : https://prove2.me/submissions/3d20c2d1-3bc5-4759-b75e-a8f311986366

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Definitions.Def_actuarial_aggregateDeductibleCeded
import Definitions.Def_actuarial_perClaimDeductibleCeded
import Definitions.Def_actuarial_aggregateDeductiblePremium
import Definitions.Def_actuarial_perClaimDeductiblePremium

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (w : ℕ → ℝ) (x : ℕ → ℕ → ℕ) (B n d : ℕ)
  (hw : ∀ s, 0 ≤ w s) :
  (perClaimDeductibleCeded (x 0) n d ≤
    aggregateDeductibleCeded (x 0) n d) ∧
  (0 ≤ aggregateDeductiblePremium w x B n d) ∧
  (perClaimDeductiblePremium w x B n d ≤
    aggregateDeductiblePremium w x B n d) := by
  have hcover (y : ℕ → ℕ) (k e : ℕ) :
      perClaimDeductibleCeded y k e ≤ aggregateDeductibleCeded y k e := by
    induction k with
    | zero =>
        simp [perClaimDeductibleCeded, aggregateDeductibleCeded, aggregateLossTotal]
    | succ k ih =>
        change (∑ i ∈ Finset.range (k + 1), (y i - e)) ≤
          (∑ i ∈ Finset.range (k + 1), y i) - e
        simp only [Finset.sum_range_succ]
        have hprev : (∑ i ∈ Finset.range k, (y i - e)) ≤
            (∑ i ∈ Finset.range k, y i) - e := ih
        omega
  constructor
  · exact hcover (x 0) n d
  constructor
  · unfold aggregateDeductiblePremium
    apply Finset.sum_nonneg
    intro s hs
    exact mul_nonneg (Nat.cast_nonneg _) (hw s)
  ·
    unfold perClaimDeductiblePremium aggregateDeductiblePremium
    apply Finset.sum_le_sum
    intro s hs
    have hcast : ((perClaimDeductibleCeded (x s) n d : ℕ) : ℝ) ≤
        ((aggregateDeductibleCeded (x s) n d : ℕ) : ℝ) := by
      exact_mod_cast hcover (x s) n d
    exact mul_le_mul_of_nonneg_right hcast (hw s)
