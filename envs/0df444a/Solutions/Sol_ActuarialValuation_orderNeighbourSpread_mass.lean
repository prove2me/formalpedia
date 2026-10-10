-- Prove2me | solution 1 for ActuarialValuation.orderNeighbourSpread_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:52:46.540988+00:00
-- url     : https://prove2.me/submissions/b8e43ced-3a7e-4332-99be-751db65f14b4

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_orderNeighbourSpread
import Definitions.Def_actuarial_orderAggregateMass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (w : ℕ → ℝ) (B c : ℕ) (delta : ℝ)
  (hlo : 0 < c) (hhi : c + 1 ≤ B) :
  orderAggregateMass (orderNeighbourSpread w c delta) B =
    orderAggregateMass w B := by
  have hiff : ∀ s : ℕ, (s + 1 = c) ↔ (s = c - 1) := by
    intro s
    omega
  have hL : (∑ s ∈ Finset.range (B + 1), (if s + 1 = c then delta / 2 else 0)) =
      delta / 2 := by
    simp only [hiff]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (by omega))]
  have hR : (∑ s ∈ Finset.range (B + 1), (if s = c + 1 then delta / 2 else 0)) =
      delta / 2 := by
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (by omega))]
  have hC : (∑ s ∈ Finset.range (B + 1), (if s = c then delta else 0)) = delta := by
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (by omega))]
  have hterm : ∀ s : ℕ, orderNeighbourSpread w c delta s =
      w s + (if s + 1 = c then delta / 2 else 0) +
      (if s = c + 1 then delta / 2 else 0) - (if s = c then delta else 0) :=
    fun s => rfl
  show (∑ s ∈ Finset.range (B + 1), orderNeighbourSpread w c delta s) =
    (∑ s ∈ Finset.range (B + 1), w s)
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hL, hR, hC]
  ring
