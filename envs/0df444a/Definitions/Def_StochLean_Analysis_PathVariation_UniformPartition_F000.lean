-- Prove2me | Definitions.Def_StochLean_Analysis_PathVariation_UniformPartition_F000
-- name    : StochLean_Analysis_PathVariation_UniformPartition_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:45:58.938004+00:00
-- url     : https://prove2.me/theorems/8a3259ac-18ba-5e33-9dee-4e491f26a678
-- title:
--   StochLean: Analysis.PathVariation.UniformPartition F000

import Definitions.Def_StochLean_Analysis_PathVariation_AdmissiblePartition_F005
import Definitions.Def_StochLean_Analysis_PathVariation_Reflection_F000
import Mathlib.Analysis.SpecificLimits.Basic

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

def uniform (δ : ℝ≥0) (hδ : 0 < δ) : LocallyFinitePartition where
  points := Set.range (fun k : ℕ ↦ (k : ℝ≥0) * δ)
  zero_mem := ⟨0, by simp⟩
  finite_bounded T := by
    obtain ⟨N, hN⟩ := exists_nat_ge (T / δ)
    apply (((Finset.range (N + 1)).finite_toSet).image (fun k : ℕ ↦ (k : ℝ≥0) * δ)).subset
    rintro t ⟨⟨k, rfl⟩, _, ht⟩
    refine ⟨k, ?_, rfl⟩
    simp only [Finset.mem_coe, Finset.mem_range]
    apply Nat.lt_succ_of_le
    exact_mod_cast (((le_div_iff₀ hδ).mpr ht).trans hN)
  unbounded := by
    rintro ⟨M, hM⟩
    obtain ⟨k, hk⟩ := exists_nat_gt (M / δ)
    have hlt : M < (k : ℝ≥0) * δ := (div_lt_iff₀ hδ).mp hk
    exact (not_le_of_gt hlt) (hM ⟨k, rfl⟩)
end StochLean.LocallyFinitePartition


