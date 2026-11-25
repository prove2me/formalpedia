-- Prove2me | Definitions.Def_SourceProof_450d12110808f2b6e6c7e25f
-- name    : SourceProof_450d12110808f2b6e6c7e25f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:19:33.523053+00:00
-- url     : https://prove2.me/theorems/e9fc5e4b-285f-5c06-8f66-adaec2f74fb5
-- title:
--   StochLean source theorem: ProbabilityTheory.strictLeftGrid_eq_of_mem_cell

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

theorem _root_.Prove2MeSourceProof.h_450d12110808f2b6e6c7e25f {δ t : ℝ≥0} (hδ : 0 < δ) (k : ℕ)
    (ht : t ∈ Ioc (δ * k) (δ * (k + 1))) : strictLeftGrid δ t = δ * k := by
  have hceil : Nat.ceil (t / δ) = k + 1 := by
    apply (Nat.ceil_eq_iff (Nat.succ_ne_zero k)).mpr
    constructor
    · simpa only [Nat.add_sub_cancel, Nat.succ_sub_one] using
        (lt_div_iff₀ hδ).mpr (by simpa only [mul_comm δ] using ht.1)
    · exact (div_le_iff₀ hδ).mpr
        (by simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_succ, mul_comm δ] using ht.2)
  simp only [ProbabilityTheory.strictLeftGrid, hceil, Nat.add_sub_cancel]
end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ}

end MeasureTheory


