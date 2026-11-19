-- Prove2me | Definitions.Def_SourceProof_7a7d131bbe1cd4c4e9ef0ba0
-- name    : SourceProof_7a7d131bbe1cd4c4e9ef0ba0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T16:58:50.526079+00:00
-- url     : https://prove2.me/theorems/c5abfd4d-77a2-4bb3-a69e-7a7e1a9af172
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Probability.indepSets_piiUnionInter_of_blocks
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.Probability.Independence.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Independence of two joins from blockwise independence

An independent family of σ-algebras, each containing two independent sub-σ-algebras, has the two
joins of those sub-σ-algebras independent: a finite intersection from each join is a single
intersection over the union of the two index sets, which the family's independence factors
blockwise and the blockwise independence factors again.
-/

open MeasureTheory MeasurableSpace ProbabilityTheory

namespace LevyStochCalc.Probability

variable {Ω ι : Type*} [DecidableEq ι] {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ]

omit [DecidableEq ι] in

theorem _root_.Prove2MeSourceProof.h_7a7d131bbe1cd4c4e9ef0ba0 {m a b : ι → MeasurableSpace Ω}
    (ha : ∀ i, a i ≤ m i) (hb : ∀ i, b i ≤ m i)
    (hm : iIndep m μ) (hab : ∀ i, Indep (a i) (b i) μ) :
    IndepSets (piiUnionInter (fun i => {t | MeasurableSet[a i] t}) Set.univ)
      (piiUnionInter (fun i => {t | MeasurableSet[b i] t}) Set.univ) μ := by
  classical
  rw [IndepSets_iff]
  rintro A B ⟨sa, -, fa, hfa, rfl⟩ ⟨sb, -, fb, hfb, rfl⟩
  have hfa'a : ∀ i, MeasurableSet[a i] (if i ∈ sa then fa i else Set.univ) := by
    intro i
    by_cases h : i ∈ sa
    · rw [if_pos h]; exact hfa i h
    · rw [if_neg h]; exact MeasurableSet.univ
  have hfb'b : ∀ i, MeasurableSet[b i] (if i ∈ sb then fb i else Set.univ) := by
    intro i
    by_cases h : i ∈ sb
    · rw [if_pos h]; exact hfb i h
    · rw [if_neg h]; exact MeasurableSet.univ
  -- the two finite intersections are a single intersection over the union
  have hsplit : (⋂ i ∈ sa, fa i) ∩ (⋂ i ∈ sb, fb i)
      = ⋂ i ∈ sa ∪ sb,
        ((if i ∈ sa then fa i else Set.univ) ∩ (if i ∈ sb then fb i else Set.univ)) := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_iInter, Finset.mem_union]
    constructor
    · rintro ⟨h1, h2⟩ i _
      refine ⟨?_, ?_⟩
      · by_cases h : i ∈ sa
        · rw [if_pos h]; exact h1 i h
        · rw [if_neg h]; trivial
      · by_cases h : i ∈ sb
        · rw [if_pos h]; exact h2 i h
        · rw [if_neg h]; trivial
    · intro h
      refine ⟨fun i hi => ?_, fun i hi => ?_⟩
      · have := (h i (Or.inl hi)).1
        rwa [if_pos hi] at this
      · have := (h i (Or.inr hi)).2
        rwa [if_pos hi] at this
  -- the same trick for each factor separately
  have hone : ∀ (s : Finset ι) (f : ι → Set Ω),
      (⋂ i ∈ s ∪ sa ∪ sb, (if i ∈ s then f i else Set.univ)) = ⋂ i ∈ s, f i := by
    intro s f
    ext ω
    simp only [Set.mem_iInter, Finset.mem_union]
    constructor
    · intro h i hi
      have := h i (Or.inl (Or.inl hi))
      rwa [if_pos hi] at this
    · intro h i _
      by_cases hi : i ∈ s
      · rw [if_pos hi]; exact h i hi
      · rw [if_neg hi]; trivial
  have hprodA : μ (⋂ i ∈ sa, fa i)
      = ∏ i ∈ sa ∪ sb, μ (if i ∈ sa then fa i else Set.univ) :=
    calc μ (⋂ i ∈ sa, fa i) = ∏ i ∈ sa, μ (fa i) :=
          hm.meas_biInter fun i hi => ha i _ (hfa i hi)
      _ = ∏ i ∈ sa, μ (if i ∈ sa then fa i else Set.univ) :=
          Finset.prod_congr rfl fun i hi => by rw [if_pos hi]
      _ = ∏ i ∈ sa ∪ sb, μ (if i ∈ sa then fa i else Set.univ) :=
          Finset.prod_subset Finset.subset_union_left
            fun x _ hx => by rw [if_neg hx, measure_univ]
  have hprodB : μ (⋂ i ∈ sb, fb i)
      = ∏ i ∈ sa ∪ sb, μ (if i ∈ sb then fb i else Set.univ) :=
    calc μ (⋂ i ∈ sb, fb i) = ∏ i ∈ sb, μ (fb i) :=
          hm.meas_biInter fun i hi => hb i _ (hfb i hi)
      _ = ∏ i ∈ sb, μ (if i ∈ sb then fb i else Set.univ) :=
          Finset.prod_congr rfl fun i hi => by rw [if_pos hi]
      _ = ∏ i ∈ sa ∪ sb, μ (if i ∈ sb then fb i else Set.univ) :=
          Finset.prod_subset Finset.subset_union_right
            fun x _ hx => by rw [if_neg hx, measure_univ]
  rw [hsplit, hm.meas_biInter (fun i _ => (ha i _ (hfa'a i)).inter (hb i _ (hfb'b i))),
    hprodA, hprodB, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact (Indep_iff _ _ _).mp (hab i) _ _ (hfa'a i) (hfb'b i)
end LevyStochCalc.Probability


