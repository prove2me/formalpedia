-- Prove2me | Definitions.Def_KLS408915f_LevyStochCalc_Probability_Augmentation
-- name    : KLS408915f_LevyStochCalc_Probability_Augmentation
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T11:12:37.143708+00:00
-- url     : https://prove2.me/theorems/912f8ed4-e901-4a17-91c4-14cc45d36b7f
-- title:
--   Augmentation of measurable spaces by null sets
-- statement:
--   Vendored from the LevyStochCalc library at https://github.com/cgarryZA/LevyStochCalc, commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. `LevyStochCalc.Probability.aug m m₀ μ` is the measurable space of sets measurable in $m₀$ that differ by a $\mu$-null symmetric difference from a set measurable in $m$. The auxiliary results `aug_le` and `aug_mono` give containment and monotonicity, and `aug_iInf_of_antitone` states that augmentation commutes with the infimum of a countable antitone sequence of measurable spaces.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/Augmentation.lean#L42-L158 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Probability.Augmentation`, definition bundle `KLS408915f_LevyStochCalc_Probability_Augmentation`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Mathlib.MeasureTheory.Measure.NullMeasurable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/Augmentation.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
open scoped symmDiff
namespace LevyStochCalc
namespace Probability
variable {Ω : Type*}
/-- The augmentation of `m` by the `μ`-null sets inside `m₀`: the `m₀`-measurable sets that
differ from an `m`-measurable set by a `μ`-null set. -/
@[reducible]
def aug (m m₀ : MeasurableSpace Ω) (μ : Measure Ω) : MeasurableSpace Ω where
  MeasurableSet' A := MeasurableSet[m₀] A ∧ ∃ B, MeasurableSet[m] B ∧ μ (A ∆ B) = 0
  measurableSet_empty := ⟨MeasurableSet.empty, ∅, @MeasurableSet.empty Ω m, by simp⟩
  measurableSet_compl := by
    rintro A ⟨hA, B, hB, hAB⟩
    refine ⟨hA.compl, Bᶜ, hB.compl, ?_⟩
    have : Aᶜ ∆ Bᶜ = A ∆ B := by
      ext x; simp only [Set.mem_symmDiff, Set.mem_compl_iff]; tauto
    rwa [this]
  measurableSet_iUnion := by
    intro f hf
    refine ⟨MeasurableSet.iUnion fun i => (hf i).1, ⋃ i, Classical.choose (hf i).2,
      MeasurableSet.iUnion fun i => (Classical.choose_spec (hf i).2).1, ?_⟩
    refine measure_mono_null Set.iUnion_symmDiff_iUnion_subset ?_
    exact measure_iUnion_null fun i => (Classical.choose_spec (hf i).2).2
variable {m m₀ : MeasurableSpace Ω} {μ : Measure Ω}
theorem aug_le : aug m m₀ μ ≤ m₀ := fun _ h => h.1
theorem aug_mono {m' : MeasurableSpace Ω} (h : m ≤ m') : aug m m₀ μ ≤ aug m' m₀ μ := by
  rintro A ⟨hA, B, hB, hAB⟩
  exact ⟨hA, B, h B hB, hAB⟩
/-- **Augmentation commutes with a countable antitone infimum.** For a decreasing sequence of
sub-σ-algebras, augmenting each and intersecting is the same as intersecting and augmenting. -/
theorem aug_iInf_of_antitone {mSeq : ℕ → MeasurableSpace Ω} (hanti : Antitone mSeq) :
    ⨅ n, aug (mSeq n) m₀ μ = aug (⨅ n, mSeq n) m₀ μ := by
  refine le_antisymm ?_ (le_iInf fun n => aug_mono (iInf_le _ n))
  intro A hA
  rw [MeasurableSpace.measurableSet_iInf] at hA
  have hA0 : MeasurableSet[m₀] A := (hA 0).1
  choose B hB hAB using fun n => (hA n).2
  set U : ℕ → Set Ω := fun N => ⋃ n, ⋃ (_ : N ≤ n), B n with hUdef
  have hUanti : Antitone U := by
    intro a b hab x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hx
    obtain ⟨hbn, hxn⟩ := Set.mem_iUnion.1 hn
    exact Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2 ⟨hab.trans hbn, hxn⟩⟩
  set C : Set Ω := ⋂ N, U N with hCdef
  refine ⟨hA0, C, ?_, ?_⟩
  · rw [MeasurableSpace.measurableSet_iInf]
    intro N
    have key : C = ⋂ k, U (N + k) := by
      refine subset_antisymm (fun x hx => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx (N + k))
        (fun x hx => Set.mem_iInter.2 fun N' => ?_)
      exact hUanti (Nat.le_add_left N' N) (Set.mem_iInter.1 hx N')
    rw [key]
    refine MeasurableSet.iInter fun k => MeasurableSet.iUnion fun n => MeasurableSet.iUnion ?_
    intro hn
    exact hanti ((Nat.le_add_right N k).trans hn) _ (hB n)
  · refine measure_mono_null ?_ (measure_iUnion_null hAB)
    intro x hx
    rcases Set.mem_symmDiff.1 hx with ⟨hxA, hxC⟩ | ⟨hxC, hxA⟩
    · obtain ⟨N, hN⟩ : ∃ N, x ∉ U N := by
        by_contra h
        exact hxC (Set.mem_iInter.2 fun N => not_not.1 fun hn => h ⟨N, hn⟩)
      refine Set.mem_iUnion.2 ⟨N, Set.mem_symmDiff.2 (Or.inl ⟨hxA, fun h => hN ?_⟩)⟩
      exact Set.mem_iUnion.2 ⟨N, Set.mem_iUnion.2 ⟨le_refl N, h⟩⟩
    · obtain ⟨n, hn⟩ := Set.mem_iUnion.1 (Set.mem_iInter.1 hxC 0)
      obtain ⟨-, hxn⟩ := Set.mem_iUnion.1 hn
      exact Set.mem_iUnion.2 ⟨n, Set.mem_symmDiff.2 (Or.inr ⟨hxn, hxA⟩)⟩
end Probability
end LevyStochCalc


