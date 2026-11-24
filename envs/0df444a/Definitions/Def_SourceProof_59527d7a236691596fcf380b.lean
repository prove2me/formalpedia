-- Prove2me | Definitions.Def_SourceProof_59527d7a236691596fcf380b
-- name    : SourceProof_59527d7a236691596fcf380b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:13:30.577705+00:00
-- url     : https://prove2.me/theorems/bebe6185-e00a-4470-9dbc-bea611ffadbd
-- title:
--   StochLean source theorem: StochLean.TimePartition.dist_tag_of_mem_cell_le_mesh

import Definitions.Def_StochLean_Analysis_PathVariation_LeftStepApproximation_F000
import Definitions.Def_SourceProof_62c96c8989b32380830efb77
import Definitions.Def_SourceProof_fc4a2bac5634cdbfe2b154e5

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Arbitrarily tagged step approximations

Tags may be either endpoint or any point between. They need not be ordered
separately from their containing cells; repeated partition endpoints are allowed.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace StochLean.TimePartition

variable {T : ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_59527d7a236691596fcf380b (π : TimePartition T) (ξ : Fin π.size → ℝ≥0)
    (hξ : ∀ i, π.left i ≤ ξ i ∧ ξ i ≤ π.right i) {t : ℝ≥0} {i : Fin π.size}
    (hi : π.left i < t ∧ t ≤ π.right i) : dist t (ξ i) ≤ (π.mesh : ℝ) := by
  have htl : (π.left i : ℝ) ≤ t := by exact_mod_cast hi.1.le
  have htr : (t : ℝ) ≤ π.right i := by exact_mod_cast hi.2
  have hξl : (π.left i : ℝ) ≤ ξ i := by exact_mod_cast (hξ i).1
  have hξr : (ξ i : ℝ) ≤ π.right i := by exact_mod_cast (hξ i).2
  calc
    dist t (ξ i) ≤ (π.right i : ℝ) - π.left i := by
      rw [NNReal.dist_eq, abs_le]
      constructor <;> linarith
    _ = (π.gap i : ℝ) := (NNReal.coe_sub ((_root_.Prove2MeSourceProof.h_fc4a2bac5634cdbfe2b154e5 π) i)).symm
    _ ≤ π.mesh := by exact_mod_cast (_root_.Prove2MeSourceProof.h_62c96c8989b32380830efb77 π) i
end StochLean.TimePartition


