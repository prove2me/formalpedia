-- Prove2me | Definitions.Def_SourceProof_84cb13b12481864682c7d2fe
-- name    : SourceProof_84cb13b12481864682c7d2fe
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:51:31.604255+00:00
-- url     : https://prove2.me/theorems/6cd8c38b-ac2c-4a41-b34c-89bf4f9be0d5
-- title:
--   StochLean source theorem: StochLean.LocallyFinitePartition.uniform_restrict_gap_le

import Definitions.Def_StochLean_Analysis_PathVariation_UniformPartition_F000
import Definitions.Def_SourceProof_100a4fbbee9cf0e8517b3b4d
import Definitions.Def_SourceProof_22d80a2190f136747d0e9643
import Definitions.Def_SourceProof_2ba9ae385eb9bd368051c43f

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Uniform infinite partitions and a concrete admissible dyadic sequence

These are actual locally finite, unbounded endpoint sets. The maximum adjacent-gap bound is
proved for every finite restriction, including the final partial cell and horizon zero.
-/

@[expose] public section

open Filter Set Finset
open scoped NNReal ENNReal Topology

namespace StochLean.LocallyFinitePartition

theorem _root_.Prove2MeSourceProof.h_84cb13b12481864682c7d2fe (δ : ℝ≥0) (hδ : 0 < δ) (T : ℝ≥0)
    (i : Fin ((uniform δ hδ).restrict T).size) :
    ((uniform δ hδ).restrict T).gap i ≤ δ := by
  let ρ := (StochLean.LocallyFinitePartition.uniform δ hδ).restrict T
  have hleft : ρ.left i = T ∨ ρ.left i ∈ (StochLean.LocallyFinitePartition.uniform δ hδ).points ∧ ρ.left i ≤ T :=
    ((_root_.Prove2MeSourceProof.h_22d80a2190f136747d0e9643 (StochLean.LocallyFinitePartition.uniform δ hδ)) T _).mp ⟨i.castSucc, rfl⟩
  rcases hleft with hleft | ⟨⟨k, hk⟩, _⟩
  · change ρ.right i - ρ.left i ≤ δ
    have hr : ρ.right i ≤ ρ.left i := ((_root_.Prove2MeSourceProof.h_2ba9ae385eb9bd368051c43f ρ) i.succ).trans_eq hleft.symm
    rw [tsub_eq_zero_of_le hr]
    exact bot_le
  · have hnext : ρ.left i + δ ∈ (StochLean.LocallyFinitePartition.uniform δ hδ).points := by
      refine ⟨k + 1, ?_⟩
      simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, hk]
    have hright : ρ.right i ≤ ρ.left i + δ := by
      by_cases hT : ρ.left i + δ ≤ T
      · have hmem := ((_root_.Prove2MeSourceProof.h_22d80a2190f136747d0e9643 (StochLean.LocallyFinitePartition.uniform δ hδ)) T _).mpr (Or.inr ⟨hnext, hT⟩)
        rcases (_root_.Prove2MeSourceProof.h_100a4fbbee9cf0e8517b3b4d ρ) hmem i with h | h
        · exact False.elim ((not_le_of_gt (lt_add_of_pos_right (ρ.left i) hδ)) h)
        · exact h
      · exact ((_root_.Prove2MeSourceProof.h_2ba9ae385eb9bd368051c43f ρ) i.succ).trans (le_of_not_ge hT)
    change ρ.right i - ρ.left i ≤ δ
    exact tsub_le_iff_right.mpr (by simpa only [add_comm] using hright)
end StochLean.LocallyFinitePartition


