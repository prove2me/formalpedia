-- Prove2me | Definitions.Def_SourceProof_f81d4c461f298be40223e563
-- name    : SourceProof_f81d4c461f298be40223e563
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:01:49.849902+00:00
-- url     : https://prove2.me/theorems/f320cc3f-cc71-4255-8b49-ba676f33c2e5
-- title:
--   StochLean source theorem: StochLean.TimePartition.dist_le_mesh_of_mem_cell

import Definitions.Def_StochLean_Analysis_PathVariation_LeftStepApproximation_F000
import Definitions.Def_SourceProof_62c96c8989b32380830efb77
import Definitions.Def_SourceProof_fc4a2bac5634cdbfe2b154e5
import Mathlib.Order.Filter.Finite

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Fine partitions separate any prescribed finite collection of times -/

@[expose] public section

open Set Filter
open scoped NNReal Topology

namespace StochLean.TimePartition

theorem _root_.Prove2MeSourceProof.h_f81d4c461f298be40223e563 {T : ℝ≥0} (π : TimePartition T) {i : Fin π.size}
    {s r : ℝ≥0} (hs : s ∈ Icc (π.left i) (π.right i))
    (hr : r ∈ Icc (π.left i) (π.right i)) : dist s r ≤ (π.mesh : ℝ) := by
  apply le_trans (b := ((StochLean.TimePartition.gap π) i : ℝ)) _ (by exact_mod_cast (_root_.Prove2MeSourceProof.h_62c96c8989b32380830efb77 π) i)
  have hsl : (π.left i : ℝ) ≤ s := by exact_mod_cast hs.1
  have hsr : (s : ℝ) ≤ π.right i := by exact_mod_cast hs.2
  have hrl : (π.left i : ℝ) ≤ r := by exact_mod_cast hr.1
  have hrr : (r : ℝ) ≤ π.right i := by exact_mod_cast hr.2
  rw [NNReal.dist_eq, StochLean.TimePartition.gap, NNReal.coe_sub ((_root_.Prove2MeSourceProof.h_fc4a2bac5634cdbfe2b154e5 π) i), abs_le]
  constructor <;> linarith only [hsl, hsr, hrl, hrr]
end StochLean.TimePartition


