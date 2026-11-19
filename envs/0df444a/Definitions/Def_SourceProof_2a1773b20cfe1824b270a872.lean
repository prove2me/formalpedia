-- Prove2me | Definitions.Def_SourceProof_2a1773b20cfe1824b270a872
-- name    : SourceProof_2a1773b20cfe1824b270a872
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:06:05.030068+00:00
-- url     : https://prove2.me/theorems/133e5e45-5e81-4121-b9c9-07c2aeee3bf1
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Probability.exists_one_le_measure_singleton
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_IntegerValuedMeasure_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Integer-valued finite measures

A measure is integer-valued when every measurable set carries a natural mass. On a measurable
space with a countable separating family such a measure, if finite, is a finite sum of Dirac
masses: a binary search along the separating family isolates a point of mass at least one, and
removing it lowers the total mass by at least one, so the recursion terminates.

Integrality on a generating π-system already gives integrality everywhere, since the sets of
natural mass form a Dynkin system as soon as the ambient measure is finite.
-/

namespace LevyStochCalc.Probability

open MeasureTheory Filter Set
open scoped ENNReal Topology

variable {α : Type*} [MeasurableSpace α]

section PiSystem

end PiSystem

section Atom

variable [MeasurableSpace.CountablySeparated α]


theorem _root_.Prove2MeSourceProof.h_2a1773b20cfe1824b270a872 (μ : Measure α) [IsFiniteMeasure μ]
    (hint : IsIntegerValued μ) (hpos : μ Set.univ ≠ 0) : ∃ x : α, 1 ≤ μ {x} := by
  classical
  obtain ⟨S, hSne, hScount, hSmeas, hSsep⟩ :=
    exists_nonempty_countable_separating α (p := MeasurableSet) MeasurableSet.univ Set.univ
  obtain ⟨f, hf⟩ := hScount.exists_eq_range hSne
  have hfS : ∀ k, f k ∈ S := fun k => by rw [hf]; exact Set.mem_range_self k
  have hfm : ∀ k, MeasurableSet (f k) := fun k => hSmeas _ (hfS k)
  set B : ℕ → Set α := fun k => Nat.recAux Set.univ
    (fun k Bk => if 1 ≤ μ (Bk ∩ f k) then Bk ∩ f k else Bk \ f k) k with hBdef
  have hB0 : B 0 = Set.univ := rfl
  have hBs : ∀ k, B (k + 1) = if 1 ≤ μ (B k ∩ f k) then B k ∩ f k else B k \ f k :=
    fun _ => rfl
  have hBm : ∀ k, MeasurableSet (B k) := by
    intro k
    induction k with
    | zero => rw [hB0]; exact MeasurableSet.univ
    | succ k ih =>
      rw [hBs k]
      by_cases hc : 1 ≤ μ (B k ∩ f k)
      · rw [if_pos hc]; exact ih.inter (hfm k)
      · rw [if_neg hc]; exact ih.diff (hfm k)
  have hBanti : Antitone B := by
    refine antitone_nat_of_succ_le fun k => ?_
    rw [hBs k]
    by_cases hc : 1 ≤ μ (B k ∩ f k)
    · rw [if_pos hc]; exact Set.inter_subset_left
    · rw [if_neg hc]; exact Set.sdiff_subset
  have hBpos : ∀ k, 1 ≤ μ (B k) := by
    intro k
    induction k with
    | zero =>
      rw [hB0]
      obtain ⟨n, hn⟩ := hint Set.univ MeasurableSet.univ
      rcases Nat.eq_zero_or_pos n with h | h
      · exact absurd (by rw [hn, h]; simp) hpos
      · rw [hn]; exact_mod_cast h
    | succ k ih =>
      rw [hBs k]
      by_cases hc : 1 ≤ μ (B k ∩ f k)
      · rw [if_pos hc]; exact hc
      · rw [if_neg hc]
        obtain ⟨m, hm⟩ := hint (B k ∩ f k) ((hBm k).inter (hfm k))
        have hm0 : μ (B k ∩ f k) = 0 := by
          rcases Nat.eq_zero_or_pos m with h | h
          · rw [hm, h]; simp
          · exact absurd (by rw [hm]; exact_mod_cast h) hc
        have hsplit : μ (B k ∩ f k) + μ (B k \ f k) = μ (B k) :=
          measure_inter_add_sdiff _ (hfm k)
        rw [hm0, zero_add] at hsplit
        rw [hsplit]; exact ih
  have hInter : 1 ≤ μ (⋂ k, B k) := by
    rw [hBanti.measure_iInter (fun k => (hBm k).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩]
    exact le_iInf hBpos
  have hsub : ∀ x y, x ∈ ⋂ k, B k → y ∈ ⋂ k, B k → x = y := by
    intro x y hx hy
    refine hSsep x (Set.mem_univ x) y (Set.mem_univ y) fun s hs => ?_
    obtain ⟨k, rfl⟩ : ∃ k, f k = s := by rw [hf] at hs; exact hs
    have hxk : x ∈ B (k + 1) := Set.mem_iInter.mp hx (k + 1)
    have hyk : y ∈ B (k + 1) := Set.mem_iInter.mp hy (k + 1)
    rw [hBs k] at hxk hyk
    by_cases hc : 1 ≤ μ (B k ∩ f k)
    · rw [if_pos hc] at hxk hyk
      exact iff_of_true hxk.2 hyk.2
    · rw [if_neg hc] at hxk hyk
      exact iff_of_false hxk.2 hyk.2
  have hne : (⋂ k, B k).Nonempty := by
    rcases Set.eq_empty_or_nonempty (⋂ k, B k) with h | h
    · rw [h] at hInter; simp at hInter
    · exact h
  obtain ⟨x, hx⟩ := hne
  exact ⟨x, le_trans hInter (measure_mono fun y hy => hsub y x hy hx)⟩
end Atom

end LevyStochCalc.Probability


