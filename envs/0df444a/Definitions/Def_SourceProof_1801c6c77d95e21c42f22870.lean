-- Prove2me | Definitions.Def_SourceProof_1801c6c77d95e21c42f22870
-- name    : SourceProof_1801c6c77d95e21c42f22870
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:44:14.519537+00:00
-- url     : https://prove2.me/theorems/ff6b7b38-fa84-5177-a713-59da5a1178ac
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.exists_finite_separators_oscillation

import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
import Definitions.Def_SourceProof_bab4ce23d252be388cfa2e27
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Small cadlag oscillations away from finitely many separating times

Compactness turns the two one-sided local limits into a finite collection
of separating points and one common distance scale. The points need not
be jumps; the assertion covers every sufficiently short interval which
does not cross any of them.
-/

@[expose] public section

open Set Filter Metric
open scoped NNReal Topology

namespace ProbabilityTheory

namespace IsCadlagPath
theorem _root_.Prove2MeSourceProof.h_1801c6c77d95e21c42f22870
    {E : Type*} [MetricSpace E] {x : ℝ≥0 → E}
    (hx : IsCadlagPath x) (T : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Finset ℝ≥0, (↑A : Set ℝ≥0) ⊆ Icc 0 T ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ a ∈ Icc 0 T, ∀ b ∈ Icc 0 T, a ≤ b → dist a b < δ →
        (∀ s ∈ A, s ∉ Ioc a b) → dist (x a) (x b) < ε := by
  classical
  choose U hU hosc using fun t ↦ (_root_.Prove2MeSourceProof.h_bab4ce23d252be388cfa2e27 hx) t hε
  obtain ⟨A, hA, hcover⟩ := (isCompact_Icc : IsCompact (Icc 0 T)).elim_nhds_subcover
    (fun t ↦ interior (U t)) (fun t _ ↦ interior_mem_nhds.mpr (hU t))
  have hcov : Icc 0 T ⊆ ⋃ s : (↑A : Set ℝ≥0), interior (U s) := by
    intro a ha
    obtain ⟨s, hs, has⟩ := mem_iUnion₂.mp (hcover ha)
    exact mem_iUnion.mpr ⟨⟨s, hs⟩, has⟩
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric isCompact_Icc
    (fun _ : (↑A : Set ℝ≥0) ↦ isOpen_interior) hcov
  refine ⟨A, fun s hs ↦ hA s hs, δ, hδ, fun a ha b _ hab hd havoid ↦ ?_⟩
  obtain ⟨s, hs⟩ := hball a ha
  have hau : a ∈ U s := interior_subset (hs (mem_ball_self hδ))
  have hbu : b ∈ U s := interior_subset (hs (by simpa only [mem_ball, dist_comm] using hd))
  apply hosc s a hau b hbu
  by_cases has : a < s
  · exact Or.inl ⟨has, lt_of_not_ge (fun hsb ↦ havoid s s.2 ⟨has, hsb⟩)⟩
  · exact Or.inr ⟨le_of_not_gt has, (le_of_not_gt has).trans hab⟩
end IsCadlagPath

end ProbabilityTheory


