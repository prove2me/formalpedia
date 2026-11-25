-- Prove2me | Definitions.Def_SourceProof_66754919dda4987b908b91db
-- name    : SourceProof_66754919dda4987b908b91db
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:11:36.055663+00:00
-- url     : https://prove2.me/theorems/edeb35fd-93ea-4996-a341-422673ff764a
-- title:
--   StochLean source theorem: StochLean.TimePartition.exists_matching_cell_of_range_eq

import Definitions.Def_SourceProof_100a4fbbee9cf0e8517b3b4d
import Definitions.Def_SourceProof_fc88d4dd547ea2e4485d2be2

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Endpoint-set invariance of deterministic sums

An ordered list may repeat its endpoints. Nonempty cells, however, are determined uniquely by
the endpoint set. Thus sums of cell contributions that vanish on empty cells depend only on
the endpoint set, rather than its enumeration.
-/

@[expose] public section

open Finset Set
open scoped NNReal

namespace StochLean.TimePartition

variable {T : ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_66754919dda4987b908b91db {π ρ : TimePartition T}
    (heq : Set.range π.point = Set.range ρ.point) {i : Fin π.size}
    (hi : π.left i < π.right i) :
    ∃ j : Fin ρ.size, ρ.left j = π.left i ∧ ρ.right j = π.right i := by
  have hmem : π.right i ∈ Set.range ρ.point := heq ▸ (show π.right i ∈ Set.range π.point
    from ⟨i.succ, rfl⟩)
  obtain ⟨j, hj, hr⟩ := (_root_.Prove2MeSourceProof.h_fc88d4dd547ea2e4485d2be2 ρ) hmem ((bot_le : 0 ≤ π.left i).trans_lt hi)
  refine ⟨j, le_antisymm ?_ ?_, hr⟩
  · have hmem' : ρ.left j ∈ Set.range π.point := heq.symm ▸
      (show ρ.left j ∈ Set.range ρ.point from ⟨j.castSucc, rfl⟩)
    rcases (_root_.Prove2MeSourceProof.h_100a4fbbee9cf0e8517b3b4d π) hmem' i with h | h
    · exact h
    · exact False.elim ((not_le_of_gt hj) h)
  · have hmem' : π.left i ∈ Set.range ρ.point := heq ▸
      (show π.left i ∈ Set.range π.point from ⟨i.castSucc, rfl⟩)
    rcases (_root_.Prove2MeSourceProof.h_100a4fbbee9cf0e8517b3b4d ρ) hmem' j with h | h
    · exact h
    · exact False.elim ((not_le_of_gt hi) (hr ▸ h))
end StochLean.TimePartition

namespace StochLean

end StochLean


