-- Prove2me | solution 1 for ActuarialValuation.frDueValue_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-13T11:40:38.76418+00:00
-- url     : https://prove2.me/submissions/6ede180f-2ebc-4ce7-b194-af1b8d4fcfea

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frDueValue

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c : ℕ → ℝ) (discount : ℝ → ℝ) (p q : ℕ → ℝ) (n m : ℕ) (hc : ∀ k ∈ Finset.range n, 0 ≤ c k) (hd : ∀ z, 0 ≤ discount z) (hp : ∀ k ∈ Finset.range n, 0 ≤ p k) (hq0 : ∀ k ∈ Finset.range n, 0 ≤ q k) (hq1 : ∀ k ∈ Finset.range n, q k ≤ 1) : 0 ≤ frDueValue c discount p q n m := by
  unfold frDueValue
  apply Finset.sum_nonneg
  intro k hk
  apply Finset.sum_nonneg
  intro j hj
  have hjlt : j < m := Finset.mem_range.mp hj
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (Nat.lt_of_le_of_lt (Nat.zero_le j) hjlt)
  have hjle : (j : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (Nat.le_of_lt hjlt)
  have hs0 : 0 ≤ (j : ℝ) / (m : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) (le_of_lt hmpos)
  have hs1 : (j : ℝ) / (m : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hmpos).2
    simpa using hjle
  have hleft : 0 ≤ 1 - (j : ℝ) / (m : ℝ) := sub_nonneg.mpr hs1
  have hright : 0 ≤ 1 - q k := sub_nonneg.mpr (hq1 k hk)
  have hproduct : 0 ≤ ((j : ℝ) / (m : ℝ)) * (1 - q k) :=
    mul_nonneg hs0 hright
  have hsurv : 0 ≤ frUddSurvival (q k) ((j : ℝ) / (m : ℝ)) := by
    unfold frUddSurvival
    nlinarith
  unfold frDueTerm
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (div_nonneg (hc k hk) (le_of_lt hmpos)) (hd _))
      (hp k hk))
    hsurv
