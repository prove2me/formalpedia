-- Prove2me | solution 1 for ActuarialValuation.orderNeighbourSpread_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:59:01.009037+00:00
-- url     : https://prove2.me/submissions/1de0fa1b-2e2e-487a-80c4-91448ef85bb7

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_orderNeighbourSpread
import Definitions.Def_actuarial_orderAggregateMean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (w : ℕ → ℝ) (B c : ℕ) (delta : ℝ)
  (hlo : 0 < c) (hhi : c + 1 ≤ B) :
  orderAggregateMean (orderNeighbourSpread w c delta) B =
    orderAggregateMean w B := by
  have hiff : ∀ s : ℕ, (s + 1 = c) ↔ (s = c - 1) := by
    intro s
    omega
  have hmL : (∑ s ∈ Finset.range (B + 1), (s : ℝ) * (if s + 1 = c then delta / 2 else 0)) =
      ((c - 1 : ℕ) : ℝ) * (delta / 2) := by
    simp only [hiff, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (by omega))]
  have hmR : (∑ s ∈ Finset.range (B + 1), (s : ℝ) * (if s = c + 1 then delta / 2 else 0)) =
      ((c + 1 : ℕ) : ℝ) * (delta / 2) := by
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (by omega))]
  have hmC : (∑ s ∈ Finset.range (B + 1), (s : ℝ) * (if s = c then delta else 0)) =
      (c : ℝ) * delta := by
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (by omega))]
  have hterm : ∀ s : ℕ, (s : ℝ) * orderNeighbourSpread w c delta s =
      (s : ℝ) * w s + (s : ℝ) * (if s + 1 = c then delta / 2 else 0) +
      (s : ℝ) * (if s = c + 1 then delta / 2 else 0) -
      (s : ℝ) * (if s = c then delta else 0) := by
    intro s
    show (s : ℝ) * (w s + (if s + 1 = c then delta / 2 else 0) +
        (if s = c + 1 then delta / 2 else 0) - (if s = c then delta else 0)) = _
    ring
  have h1c : 1 ≤ c := hlo
  have hcast : ((c - 1 : ℕ) : ℝ) = (c : ℝ) - 1 := by rw [Nat.cast_sub h1c, Nat.cast_one]
  show (∑ s ∈ Finset.range (B + 1), (s : ℝ) * orderNeighbourSpread w c delta s) =
    (∑ s ∈ Finset.range (B + 1), (s : ℝ) * w s)
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hmL, hmR, hmC, hcast]
  push_cast
  ring
