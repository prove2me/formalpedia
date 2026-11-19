-- Prove2me | Definitions.Def_SourceProof_3d9324e122196ddc3f47a23f
-- name    : SourceProof_3d9324e122196ddc3f47a23f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:06:19.087412+00:00
-- url     : https://prove2.me/theorems/5f67f286-a62e-4c5e-b6ce-8b17c84e3ed6
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Probability.isIntegerValued_of_isPiSystem
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


theorem _root_.Prove2MeSourceProof.h_3d9324e122196ddc3f47a23f {μ : Measure α} [IsFiniteMeasure μ] {C : Set (Set α)}
    (hgen : ‹MeasurableSpace α› = MeasurableSpace.generateFrom C) (hpi : IsPiSystem C)
    (hC : ∀ B ∈ C, ∃ n : ℕ, μ B = n) (huniv : ∃ N : ℕ, μ Set.univ = N) :
    IsIntegerValued μ := by
  intro B hB
  refine MeasurableSpace.induction_on_inter (C := fun t _ => ∃ n : ℕ, μ t = n) hgen hpi
    ⟨0, by simp⟩ (fun t ht => hC t ht) ?_ ?_ B hB
  · rintro t htm ⟨n, hn⟩
    obtain ⟨N, hN⟩ := huniv
    have hle : n ≤ N := by
      have hmono : (n : ℝ≥0∞) ≤ (N : ℝ≥0∞) := by
        rw [← hn, ← hN]; exact measure_mono (Set.subset_univ t)
      exact_mod_cast hmono
    refine ⟨N - n, ?_⟩
    have hsum : (n : ℝ≥0∞) + ((N - n : ℕ) : ℝ≥0∞) = (N : ℝ≥0∞) := by
      rw [← Nat.cast_add, Nat.add_sub_cancel' hle]
    have hcancel : (n : ℝ≥0∞) + μ tᶜ = (n : ℝ≥0∞) + ((N - n : ℕ) : ℝ≥0∞) := by
      rw [hsum, ← hN, ← measure_add_measure_compl htm, hn]
    exact (ENNReal.add_right_inj (by simp)).mp hcancel
  · intro f hdisj hfm hf
    choose g hg using hf
    obtain ⟨N, hN⟩ := huniv
    have hpart : ∀ k : ℕ, ((∑ i ∈ Finset.range k, g i : ℕ) : ℝ≥0∞)
        = μ (⋃ i ∈ Finset.range k, f i) := by
      intro k
      rw [measure_biUnion_finset (fun i _ j _ hij => hdisj hij) fun i _ => hfm i]
      push_cast
      exact Finset.sum_congr rfl fun i _ => (hg i).symm
    have hFle : ∀ k : ℕ, (∑ i ∈ Finset.range k, g i) ≤ N := by
      intro k
      have h2 : μ (⋃ i ∈ Finset.range k, f i) ≤ (N : ℝ≥0∞) :=
        hN ▸ measure_mono (Set.subset_univ _)
      have h3 : ((∑ i ∈ Finset.range k, g i : ℕ) : ℝ≥0∞) ≤ (N : ℝ≥0∞) := (hpart k).symm ▸ h2
      exact_mod_cast h3
    have hbdd : BddAbove (Set.range fun k => ∑ i ∈ Finset.range k, g i) :=
      ⟨N, by rintro _ ⟨k, rfl⟩; exact hFle k⟩
    have hmem := Nat.sSup_mem (Set.range_nonempty _) hbdd
    obtain ⟨k₀, hk₀⟩ := hmem
    refine ⟨∑ i ∈ Finset.range k₀, g i, ?_⟩
    rw [measure_iUnion hdisj hfm, ENNReal.tsum_eq_iSup_nat]
    refine le_antisymm (iSup_le fun k => ?_) ?_
    · have hsum : ∑ i ∈ Finset.range k, μ (f i) = ((∑ i ∈ Finset.range k, g i : ℕ) : ℝ≥0∞) := by
        push_cast
        exact Finset.sum_congr rfl fun i _ => hg i
      rw [hsum]
      have hk₀' : (∑ i ∈ Finset.range k₀, g i)
          = sSup (Set.range fun k => ∑ i ∈ Finset.range k, g i) := hk₀
      have hle' : (∑ i ∈ Finset.range k, g i) ≤ ∑ i ∈ Finset.range k₀, g i := by
        rw [hk₀']; exact le_csSup hbdd ⟨k, rfl⟩
      exact_mod_cast hle'
    · have hsum : ∑ i ∈ Finset.range k₀, μ (f i) = ((∑ i ∈ Finset.range k₀, g i : ℕ) : ℝ≥0∞) := by
        push_cast
        exact Finset.sum_congr rfl fun i _ => hg i
      exact hsum ▸ le_iSup (fun k => ∑ i ∈ Finset.range k, μ (f i)) k₀
end PiSystem

section Atom

variable [MeasurableSpace.CountablySeparated α]

end Atom

end LevyStochCalc.Probability


