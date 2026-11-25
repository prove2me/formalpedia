-- Prove2me | Definitions.Def_SourceProof_7a587c2d7b097459d1fe61a8
-- name    : SourceProof_7a587c2d7b097459d1fe61a8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:41:21.13494+00:00
-- url     : https://prove2.me/theorems/5efb8951-bd36-41b0-b400-e2d6e8cd79dc
-- title:
--   StochLean source theorem: ProbabilityTheory.strictLeftGrid_mem_cell

import Definitions.Def_StochLean_Probability_Process_Measurability_PredictableGrid_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Strict-past deterministic grids for predictable processes

At a positive grid endpoint the preceding cell is used, as required for predictable
`(s,t]` rectangles. At zero the original initial value is retained.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

theorem _root_.Prove2MeSourceProof.h_7a587c2d7b097459d1fe61a8 {δ t : ℝ≥0} (hδ : 0 < δ) (ht : 0 < t) :
    t ∈ Ioc (strictLeftGrid δ t) (strictLeftGrid δ t + δ) := by
  have hn : 0 < Nat.ceil (t / δ) := Nat.ceil_pos.mpr (div_pos ht hδ)
  have hs : Nat.ceil (t / δ) - 1 + 1 = Nat.ceil (t / δ) := Nat.sub_add_cancel hn
  have hlo : ((Nat.ceil (t / δ) - 1 : ℕ) : ℝ≥0) < t / δ :=
    Nat.lt_ceil.mp (Nat.sub_lt hn (by decide))
  have hhi := Nat.le_ceil (t / δ)
  constructor
  · simpa only [ProbabilityTheory.strictLeftGrid, mul_comm δ] using (lt_div_iff₀ hδ).mp hlo
  · have h := (div_le_iff₀ hδ).mp hhi
    have heq : (Nat.ceil (t / δ) : ℝ≥0) = ((Nat.ceil (t / δ) - 1 : ℕ) : ℝ≥0) + 1 := by
      exact_mod_cast hs.symm
    simpa only [heq, add_mul, one_mul, ProbabilityTheory.strictLeftGrid, mul_comm δ] using h
end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ}

end MeasureTheory


