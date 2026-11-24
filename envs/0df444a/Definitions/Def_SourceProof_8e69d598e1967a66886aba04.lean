-- Prove2me | Definitions.Def_SourceProof_8e69d598e1967a66886aba04
-- name    : SourceProof_8e69d598e1967a66886aba04
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:46:05.841439+00:00
-- url     : https://prove2.me/theorems/586cfc48-12a2-4657-958a-4ea660816fe5
-- title:
--   StochLean source theorem: StochLean.normSquareVariationSum_pi_le

import Definitions.Def_StochLean_Analysis_PathVariation_VectorEnergy_F000
import Definitions.Def_SourceProof_22d7c20cd70c853ad39533f6

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Vector increment energies bounded by the existing coordinate square sums

These are deterministic finite sums, not a new stochastic bracket. The finite
product uses Mathlib's sup norm; domination by coordinate squares also covers
the empty coordinate type.
-/

@[expose] public section

open Finset Filter
open scoped NNReal

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_8e69d598e1967a66886aba04 {ι : Type*} [Fintype ι]
    {T : ℝ≥0} (π : TimePartition T) (x : ℝ≥0 → ι → ℝ) :
    normSquareVariationSum π x ≤ ∑ j, quadraticVariationSum π (fun t ↦ x t j) := by
  calc
    _ ≤ ∑ i : Fin π.size, ∑ j, (x (π.right i) j - x (π.left i) j) ^ 2 :=
      sum_le_sum (fun i _ ↦ _root_.Prove2MeSourceProof.h_22d7c20cd70c853ad39533f6 (x (π.right i) - x (π.left i)))
    _ = _ := by rw [sum_comm]; rfl
end StochLean


