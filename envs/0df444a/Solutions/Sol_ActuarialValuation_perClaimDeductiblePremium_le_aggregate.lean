-- Prove2me | solution 1 for ActuarialValuation.perClaimDeductiblePremium_le_aggregate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:07:03.392481+00:00
-- url     : https://prove2.me/submissions/a5917e9f-da35-4da5-853a-bf4bfbac6b8a

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
  perClaimDeductiblePremium w x B n d ≤
    aggregateDeductiblePremium w x B n d := by
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
  unfold perClaimDeductiblePremium aggregateDeductiblePremium
  apply Finset.sum_le_sum
  intro s hs
  have hcast : ((perClaimDeductibleCeded (x s) n d : ℕ) : ℝ) ≤
      ((aggregateDeductibleCeded (x s) n d : ℕ) : ℝ) := by
    exact_mod_cast hcover (x s) n d
  exact mul_le_mul_of_nonneg_right hcast (hw s)
