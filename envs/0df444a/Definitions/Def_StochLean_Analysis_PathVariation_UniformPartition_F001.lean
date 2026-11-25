-- Prove2me | Definitions.Def_StochLean_Analysis_PathVariation_UniformPartition_F001
-- name    : StochLean_Analysis_PathVariation_UniformPartition_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:50:43.026047+00:00
-- url     : https://prove2.me/theorems/d0342511-ee11-46c5-a9d2-1de36255a4bc
-- title:
--   StochLean: Analysis.PathVariation.UniformPartition F001

import Definitions.Def_StochLean_Analysis_PathVariation_UniformPartition_F000

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

noncomputable def dyadic (n : ℕ) : LocallyFinitePartition :=
  uniform ((1 / 2 : ℝ≥0) ^ n) (pow_pos (by norm_num) n)
end StochLean.LocallyFinitePartition


