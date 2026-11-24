-- Prove2me | Definitions.Def_SourceProof_eaa152490266b02f7461a510
-- name    : SourceProof_eaa152490266b02f7461a510
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:57:24.752799+00:00
-- url     : https://prove2.me/theorems/9417de53-f71d-45ff-97d3-ea7ddb5f6010
-- title:
--   StochLean source theorem: StochLean.TimePartition.dist_right_left_eq_gap

import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F002
import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F003
import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F005
import Definitions.Def_SourceProof_fc4a2bac5634cdbfe2b154e5
import Mathlib.Topology.UniformSpace.HeineCantor

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Vanishing increments on fine deterministic partitions -/

@[expose] public section

open Filter Finset Set
open scoped NNReal Topology

namespace StochLean.TimePartition

variable {T : ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_eaa152490266b02f7461a510 (π : TimePartition T) (i : Fin π.size) :
    dist (π.right i) (π.left i) = (π.gap i : ℝ) := by
  change |(π.right i : ℝ) - (π.left i : ℝ)| = (π.gap i : ℝ)
  rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast (_root_.Prove2MeSourceProof.h_fc4a2bac5634cdbfe2b154e5 π) i))]
  exact (NNReal.coe_sub ((_root_.Prove2MeSourceProof.h_fc4a2bac5634cdbfe2b154e5 π) i)).symm
end StochLean.TimePartition


