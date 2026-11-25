-- Prove2me | Definitions.Def_SourceProof_9da775080899de8b87d4743f
-- name    : SourceProof_9da775080899de8b87d4743f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:57:08.783748+00:00
-- url     : https://prove2.me/theorems/6434b7e5-d92d-4c0a-a92f-6c7650743f9b
-- title:
--   StochLean source theorem: StochLean.LocallyFinitePartition.dyadic_points_monotone

import Definitions.Def_StochLean_Analysis_PathVariation_UniformPartition_F001

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

theorem _root_.Prove2MeSourceProof.h_9da775080899de8b87d4743f : Monotone (fun n ↦ (dyadic n).points) := by
  apply monotone_nat_of_le_succ
  intro n x hx
  obtain ⟨k, hk⟩ := hx
  refine ⟨2 * k, ?_⟩
  change ((2 * k : ℕ) : ℝ≥0) * (1 / 2 : ℝ≥0) ^ (n + 1) = x
  rw [← hk]
  push_cast
  rw [pow_succ]
  ring
end StochLean.LocallyFinitePartition


