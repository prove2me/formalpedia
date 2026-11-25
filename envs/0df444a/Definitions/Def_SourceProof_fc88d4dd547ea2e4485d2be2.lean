-- Prove2me | Definitions.Def_SourceProof_fc88d4dd547ea2e4485d2be2
-- name    : SourceProof_fc88d4dd547ea2e4485d2be2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:01:50.689198+00:00
-- url     : https://prove2.me/theorems/ed51977d-5c24-4ee2-b48f-d277c1f8021b
-- title:
--   StochLean source theorem: StochLean.TimePartition.exists_cell_right_of_mem

import Definitions.Def_StochLean_Analysis_PathVariation_Approximation_F000
import Definitions.Def_StochLean_Analysis_PathVariation_Reflection_F000
import Definitions.Def_SourceProof_2ba9ae385eb9bd368051c43f
import Definitions.Def_SourceProof_41c8e0f72444e5cb2bd104fc
import Definitions.Def_SourceProof_d90de18cdaae59a2bf0af35c

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

theorem _root_.Prove2MeSourceProof.h_fc88d4dd547ea2e4485d2be2 (π : TimePartition T) {t : ℝ≥0}
    (ht : t ∈ Set.range π.point) (hpos : 0 < t) :
    ∃ i : Fin π.size, π.left i < t ∧ π.right i = t := by
  obtain ⟨k, hk⟩ := ht
  have htT : t ≤ T := hk ▸ (_root_.Prove2MeSourceProof.h_2ba9ae385eb9bd368051c43f π) k
  have hcle : (StochLean.TimePartition.ceilingPoint π) t ≤ t := by
    rw [← hk]
    exact π.monotone_point ((_root_.Prove2MeSourceProof.h_d90de18cdaae59a2bf0af35c π) (min_le_left _ _))
  have hceq : (StochLean.TimePartition.ceilingPoint π) t = t :=
    le_antisymm hcle (by simpa only [min_eq_left htT] using (_root_.Prove2MeSourceProof.h_41c8e0f72444e5cb2bd104fc π) t)
  have hne : π.ceilingIndex t ≠ 0 := by
    intro h
    have hz : (StochLean.TimePartition.ceilingPoint π) t = 0 := by simp [StochLean.TimePartition.ceilingPoint, h, π.first_eq_zero]
    exact (ne_of_gt hpos) (hceq.symm.trans hz)
  let i : Fin π.size := (π.ceilingIndex t).pred hne
  refine ⟨i, ?_, ?_⟩
  · apply lt_of_not_ge
    intro hle
    have hmin := (_root_.Prove2MeSourceProof.h_d90de18cdaae59a2bf0af35c (i := i.castSucc) π) ((min_le_left t T).trans hle)
    have hlt : i.castSucc < π.ceilingIndex t := by
      simpa [i] using (Fin.castSucc_lt_succ (i := i))
    exact (not_le_of_gt hlt) hmin
  · simpa [StochLean.TimePartition.right, i, StochLean.TimePartition.ceilingPoint] using hceq
end StochLean.TimePartition

namespace StochLean

end StochLean


