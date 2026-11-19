-- Prove2me | Definitions.Def_SourceProof_17683012ceda8988fdc379c5
-- name    : SourceProof_17683012ceda8988fdc379c5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T17:01:11.181618+00:00
-- url     : https://prove2.me/theorems/adc2f155-f04f-4c95-b37e-61925fee54cc
-- title:
--   LevyStochCalc source proof: MeasureTheory.exists_alternating_of_le_upcrossingsBefore
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.Probability.Martingale.Upcrossing

/-
Copyright (c) 2026 Rohit Manokaran. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohit Manokaran
-/

@[expose] public section

namespace MeasureTheory

variable {ι Ω β : Type*} {mΩ : MeasurableSpace Ω}
  {f g : ℕ → Ω → ℝ} {a b : ℝ} {N : ℕ} {ω : Ω}


theorem _root_.Prove2MeSourceProof.h_17683012ceda8988fdc379c5 (hab : a < b) {m : ℕ}
    (hm : m ≤ upcrossingsBefore a b f N ω) :
    ∃ c : ℕ → ℕ, (∀ i, i + 1 < 2 * m → c i < c (i + 1)) ∧ (∀ i < 2 * m, c i < N)
      ∧ (∀ i < m, f (c (2 * i)) ω ≤ a) ∧ (∀ i < m, b ≤ f (c (2 * i + 1)) ω) := by
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · exact ⟨fun _ ↦ 0, by simp, by simp, by simp, by simp⟩
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with rfl | h
    · rw [upcrossingsBefore_zero] at hm; lia
    · exact h
  have hLlt : ∀ n, n < m → lowerCrossingTime a b f N n ω < N := fun n hn ↦
    lowerCrossingTime_lt_of_lt_upcrossingsBefore hNpos hab (hn.trans_le hm)
  have hUlt : ∀ n, n ≤ m → upperCrossingTime a b f N n ω < N := fun n hn ↦
    upperCrossingTime_lt_of_le_upcrossingsBefore hNpos hab (hn.trans hm)
  set idx : ℕ → ℕ :=
    fun i ↦ if Even i then lowerCrossingTime a b f N (i / 2) ω
      else upperCrossingTime a b f N (i / 2 + 1) ω with hidx
  have he : ∀ j, idx (2 * j) = lowerCrossingTime a b f N j ω := by
    intro j
    simp only [hidx]
    rw [if_pos (even_two.mul_right j), show 2 * j / 2 = j from by omega]
  have ho : ∀ j, idx (2 * j + 1) = upperCrossingTime a b f N (j + 1) ω := by
    intro j
    simp only [hidx]
    rw [if_neg (Nat.not_even_iff_odd.mpr ⟨j, rfl⟩ : ¬ Even (2 * j + 1)),
      show (2 * j + 1) / 2 = j from by omega]
  refine ⟨idx, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rcases Nat.even_or_odd i with hev | hodd
    · have hev2 : i % 2 = 0 := Nat.even_iff.mp hev
      have e1 : idx i = lowerCrossingTime a b f N (i / 2) ω := by
        simp only [hidx]; rw [if_pos hev]
      have e2 : idx (i + 1) = upperCrossingTime a b f N (i / 2 + 1) ω := by
        simp only [hidx]
        rw [if_neg (Nat.not_even_iff_odd.mpr hev.add_one : ¬ Even (i + 1)),
          show (i + 1) / 2 = i / 2 from by omega]
      rw [e1, e2]
      exact lowerCrossingTime_lt_upperCrossingTime hab (ne_of_lt (hUlt _ (by omega)))
    · have hodd2 : i % 2 = 1 := Nat.odd_iff.mp hodd
      have e1 : idx i = upperCrossingTime a b f N (i / 2 + 1) ω := by
        simp only [hidx]; rw [if_neg (Nat.not_even_iff_odd.mpr hodd)]
      have e2 : idx (i + 1) = lowerCrossingTime a b f N (i / 2 + 1) ω := by
        simp only [hidx]
        rw [if_pos (hodd.add_one : Even (i + 1)), show (i + 1) / 2 = i / 2 + 1 from by omega]
      rw [e1, e2]
      exact upperCrossingTime_lt_lowerCrossingTime hab (ne_of_lt (hLlt _ (by omega)))
  · intro i hi
    rcases Nat.even_or_odd i with hev | hodd
    · have e1 : idx i = lowerCrossingTime a b f N (i / 2) ω := by
        simp only [hidx]; rw [if_pos hev]
      rw [e1]; exact hLlt _ (by omega)
    · have e1 : idx i = upperCrossingTime a b f N (i / 2 + 1) ω := by
        simp only [hidx]; rw [if_neg (Nat.not_even_iff_odd.mpr hodd)]
      rw [e1]; exact hUlt _ (by omega)
  · intro i hi
    rw [he i]
    exact stoppedValue_lowerCrossingTime (ne_of_lt (hLlt i hi))
  · intro i hi
    rw [ho i]
    exact stoppedValue_upperCrossingTime (ne_of_lt (hUlt (i + 1) hi))
end MeasureTheory


