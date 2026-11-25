-- Prove2me | Definitions.Def_SourceProof_36da4c661fc115cbdc2bfff4
-- name    : SourceProof_36da4c661fc115cbdc2bfff4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:02:15.050557+00:00
-- url     : https://prove2.me/theorems/519dd2bc-a623-46a7-b009-3e94341e55dd
-- title:
--   StochLean source theorem: StochLean.LocallyFinitePartition.dyadic_admissible

import Definitions.Def_StochLean_Analysis_PathVariation_UniformPartition_F001
import Definitions.Def_SourceProof_9da775080899de8b87d4743f
import Definitions.Def_SourceProof_d2c197c32fd38fcc8a5c7fc1

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

theorem _root_.Prove2MeSourceProof.h_36da4c661fc115cbdc2bfff4 : IsAdmissiblePartitionSequence dyadic := by
  refine ⟨_root_.Prove2MeSourceProof.h_9da775080899de8b87d4743f, ?_⟩
  have hlim : Tendsto (fun n ↦ (((1 / 2 : ℝ≥0) ^ n) : ℝ≥0∞)) atTop (𝓝 0) :=
    ENNReal.tendsto_coe.mpr (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ ↦ bot_le) (fun n ↦ _root_.Prove2MeSourceProof.h_d2c197c32fd38fcc8a5c7fc1 _ _)
end StochLean.LocallyFinitePartition


