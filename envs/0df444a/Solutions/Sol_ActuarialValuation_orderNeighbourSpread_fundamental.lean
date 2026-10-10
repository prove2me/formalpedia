-- Prove2me | solution 1 for ActuarialValuation.orderNeighbourSpread_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:16:54.795964+00:00
-- url     : https://prove2.me/submissions/7f815ada-c643-4772-a493-2a74726b6cea

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_orderNeighbourSpread
import Definitions.Def_actuarial_orderAggregateMass
import Definitions.Def_actuarial_orderAggregateMean
import Definitions.Def_actuarial_orderStopLossDominates
import Definitions.Def_actuarial_orderStopLossPremium
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (w : ℕ → ℝ) (B c : ℕ) (delta : ℝ)
  (hlo : 0 < c) (hhi : c + 1 ≤ B)
  (hw : ∀ s, 0 ≤ w s) (hd : 0 ≤ delta) (hcap : delta ≤ w c) :
  (∀ s, 0 ≤ orderNeighbourSpread w c delta s) ∧
  (orderAggregateMass (orderNeighbourSpread w c delta) B =
    orderAggregateMass w B) ∧
  (orderAggregateMean (orderNeighbourSpread w c delta) B =
    orderAggregateMean w B) ∧
  orderStopLossDominates w (orderNeighbourSpread w c delta) B := by
  have hiff : ∀ s : ℕ, (s + 1 = c) ↔ (s = c - 1) := by
    intro s
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    show 0 ≤ w s + (if s + 1 = c then delta / 2 else 0) +
        (if s = c + 1 then delta / 2 else 0) - (if s = c then delta else 0)
    by_cases h3 : s = c
    · rw [h3]
      have eT : (if c = c then delta else (0 : ℝ)) = delta := if_pos rfl
      have f1 : c + 1 ≠ c := by omega
      have f2 : c ≠ c + 1 := by omega
      rw [eT, if_neg f1, if_neg f2]
      linarith [hcap]
    · have eC : (if s = c then delta else (0 : ℝ)) = 0 := if_neg h3
      rw [eC]
      split_ifs with h1 h2 <;> linarith [hw s, hd]
  · have hL : (∑ s ∈ Finset.range (B + 1), (if s + 1 = c then delta / 2 else 0)) =
        delta / 2 := by
      simp only [hiff];       rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (by omega))]
    have hR : (∑ s ∈ Finset.range (B + 1), (if s = c + 1 then delta / 2 else 0)) =
        delta / 2 := by
      rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (by omega))]
    have hC : (∑ s ∈ Finset.range (B + 1), (if s = c then delta else 0)) = delta := by
      rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (by omega))]
    have hterm : ∀ s : ℕ, orderNeighbourSpread w c delta s =
        w s + (if s + 1 = c then delta / 2 else 0) +
        (if s = c + 1 then delta / 2 else 0) - (if s = c then delta else 0) := fun s => rfl
    show (∑ s ∈ Finset.range (B + 1), orderNeighbourSpread w c delta s) =
      (∑ s ∈ Finset.range (B + 1), w s)
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hL, hR, hC]
    ring
  · have hmL : (∑ s ∈ Finset.range (B + 1), (s : ℝ) * (if s + 1 = c then delta / 2 else 0)) =
        ((c - 1 : ℕ) : ℝ) * (delta / 2) := by
      simp only [hiff, mul_ite, mul_zero];       rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (by omega))]
    have hmR : (∑ s ∈ Finset.range (B + 1), (s : ℝ) * (if s = c + 1 then delta / 2 else 0)) =
        ((c + 1 : ℕ) : ℝ) * (delta / 2) := by
      simp only [mul_ite, mul_zero];       rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (by omega))]
    have hmC : (∑ s ∈ Finset.range (B + 1), (s : ℝ) * (if s = c then delta else 0)) =
        (c : ℝ) * delta := by
      simp only [mul_ite, mul_zero];       rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (by omega))]
    have hmterm : ∀ s : ℕ, (s : ℝ) * orderNeighbourSpread w c delta s =
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
    simp only [hmterm, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hmL, hmR, hmC, hcast]
    push_cast
    ring
  · intro d
    show orderStopLossPremium w B d ≤
      orderStopLossPremium (orderNeighbourSpread w c delta) B d
    have hsL : (∑ s ∈ Finset.range (B + 1), ((s - d : ℕ) : ℝ) * (if s + 1 = c then delta / 2 else 0)) =
        ((c - 1 - d : ℕ) : ℝ) * (delta / 2) := by
      simp only [hiff, mul_ite, mul_zero];       rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (by omega))]
    have hsR : (∑ s ∈ Finset.range (B + 1), ((s - d : ℕ) : ℝ) * (if s = c + 1 then delta / 2 else 0)) =
        ((c + 1 - d : ℕ) : ℝ) * (delta / 2) := by
      simp only [mul_ite, mul_zero];       rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (by omega))]
    have hsC : (∑ s ∈ Finset.range (B + 1), ((s - d : ℕ) : ℝ) * (if s = c then delta else 0)) =
        ((c - d : ℕ) : ℝ) * delta := by
      simp only [mul_ite, mul_zero];       rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (by omega))]
    have hsterm : ∀ s : ℕ, ((s - d : ℕ) : ℝ) * orderNeighbourSpread w c delta s =
        ((s - d : ℕ) : ℝ) * w s +
        (((s - d : ℕ) : ℝ) * (if s + 1 = c then delta / 2 else 0) +
        ((s - d : ℕ) : ℝ) * (if s = c + 1 then delta / 2 else 0) -
        ((s - d : ℕ) : ℝ) * (if s = c then delta else 0)) := by
      intro s
      show ((s - d : ℕ) : ℝ) * (w s + (if s + 1 = c then delta / 2 else 0) +
          (if s = c + 1 then delta / 2 else 0) - (if s = c then delta else 0)) = _
      ring
    have h2nd : 0 ≤ ((c - 1 - d : ℕ) : ℝ) + ((c + 1 - d : ℕ) : ℝ) -
        2 * ((c - d : ℕ) : ℝ) := by
      rcases lt_or_ge d c with hdc | hdc
      · have e1 : c - 1 - d + 1 = c - d := by omega
        have e2 : c + 1 - d = (c - 1 - d) + 2 := by omega
        have r1 : ((c - d : ℕ) : ℝ) = ((c - 1 - d : ℕ) : ℝ) + 1 := by
          rw [← e1]
          push_cast
          ring
        have r2 : ((c + 1 - d : ℕ) : ℝ) = ((c - 1 - d : ℕ) : ℝ) + 2 := by
          rw [e2]
          push_cast
          ring
        have heq : ((c - 1 - d : ℕ) : ℝ) + ((c + 1 - d : ℕ) : ℝ) -
            2 * ((c - d : ℕ) : ℝ) = 0 := by
          rw [r1, r2]
          ring
        rw [heq]
      · rcases eq_or_lt_of_le hdc with heq | hlt
        · rw [heq]
          have a0 : d - 1 - d = 0 := by omega
          have b1 : d + 1 - d = 1 := by omega
          have e0 : d - d = 0 := Nat.sub_self d
          rw [a0, b1, e0]
          norm_num
        · have a0 : c - 1 - d = 0 := by omega
          have b0 : c + 1 - d = 0 := by omega
          have e0 : c - d = 0 := by omega
          rw [a0, b0, e0]
          simp
    have hge : 0 ≤ orderStopLossPremium (orderNeighbourSpread w c delta) B d -
        orderStopLossPremium w B d := by
      show 0 ≤ (∑ s ∈ Finset.range (B + 1), ((s - d : ℕ) : ℝ) *
          orderNeighbourSpread w c delta s) -
        (∑ s ∈ Finset.range (B + 1), ((s - d : ℕ) : ℝ) * w s)
      simp only [hsterm, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [hsL, hsR, hsC]
      have hnn := mul_nonneg (show (0 : ℝ) ≤ delta / 2 by linarith) h2nd
      linarith
    linarith
