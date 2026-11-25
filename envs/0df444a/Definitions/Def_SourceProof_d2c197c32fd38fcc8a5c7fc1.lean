-- Prove2me | Definitions.Def_SourceProof_d2c197c32fd38fcc8a5c7fc1
-- name    : SourceProof_d2c197c32fd38fcc8a5c7fc1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:56:57.78191+00:00
-- url     : https://prove2.me/theorems/d67fd052-d29f-5c15-a091-e03887b13ee8
-- title:
--   StochLean source theorem: StochLean.LocallyFinitePartition.uniform_mesh_le

import Definitions.Def_StochLean_Analysis_PathVariation_UniformPartition_F000
import Definitions.Def_SourceProof_84cb13b12481864682c7d2fe

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

theorem _root_.Prove2MeSourceProof.h_d2c197c32fd38fcc8a5c7fc1 (δ : ℝ≥0) (hδ : 0 < δ) : (uniform δ hδ).mesh ≤ (δ : ℝ≥0∞) := by
  apply iSup_le
  intro T
  apply ENNReal.coe_le_coe.mpr
  exact Finset.sup_le (fun i _ ↦ _root_.Prove2MeSourceProof.h_84cb13b12481864682c7d2fe δ hδ T i)
end StochLean.LocallyFinitePartition


