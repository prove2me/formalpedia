-- Prove2me | Definitions.Def_SourceProof_3b43603c6d152d29eb5ba64d
-- name    : SourceProof_3b43603c6d152d29eb5ba64d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:38:11.783357+00:00
-- url     : https://prove2.me/theorems/e992e14c-7073-4b58-b15e-458899d4402c
-- title:
--   StochLean source theorem: StochLean.TimePartition.sum_nonempty_cells

import Definitions.Def_StochLean_Analysis_PathVariation_Approximation_F000
import Definitions.Def_StochLean_Analysis_PathVariation_Approximation_F002
import Definitions.Def_StochLean_Analysis_PathVariation_Reflection_F000
import Definitions.Def_SourceProof_fc4a2bac5634cdbfe2b154e5

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

theorem _root_.Prove2MeSourceProof.h_3b43603c6d152d29eb5ba64d {E : Type*} [AddCommMonoid E] (π : TimePartition T)
    (F : ℝ≥0 → ℝ≥0 → E) (hF : ∀ t, F t t = 0) :
    (∑ i ∈ univ.filter (fun i ↦ π.left i < π.right i), F (π.left i) (π.right i)) =
      ∑ i, F (π.left i) (π.right i) := by
  classical
  apply sum_subset (filter_subset _ _)
  intro i _ hi
  have hle : π.right i ≤ π.left i := by simpa only [mem_filter, Finset.mem_univ, true_and,
    not_lt] using hi
  rw [le_antisymm ((_root_.Prove2MeSourceProof.h_fc4a2bac5634cdbfe2b154e5 π) i) hle, hF]
end StochLean.TimePartition

namespace StochLean

end StochLean


