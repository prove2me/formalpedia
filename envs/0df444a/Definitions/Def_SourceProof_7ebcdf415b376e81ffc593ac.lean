-- Prove2me | Definitions.Def_SourceProof_7ebcdf415b376e81ffc593ac
-- name    : SourceProof_7ebcdf415b376e81ffc593ac
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:15:41.234012+00:00
-- url     : https://prove2.me/theorems/b49a5c45-b9a3-46cb-8fc0-366037663258
-- title:
--   StochLean source theorem: StochLean.TimePartition.dist_left_of_mem_cell_le_mesh

import Definitions.Def_StochLean_Analysis_PathVariation_Approximation_F000
import Definitions.Def_StochLean_Analysis_PathVariation_Approximation_F002
import Definitions.Def_SourceProof_62c96c8989b32380830efb77
import Definitions.Def_SourceProof_eaa152490266b02f7461a510
import Definitions.Def_SourceProof_fc4a2bac5634cdbfe2b154e5
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Left-endpoint step approximation on a finite partition

Cells are left-open and right-closed. Repeated endpoints are permitted: every
positive time before the horizon belongs to exactly one nonempty cell.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace StochLean.TimePartition

variable {T : ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_7ebcdf415b376e81ffc593ac (π : TimePartition T) {t : ℝ≥0} {i : Fin π.size}
    (hi : π.left i < t ∧ t ≤ π.right i) : dist t (π.left i) ≤ (π.mesh : ℝ) := by
  calc
    dist t (π.left i) ≤ dist (π.right i) (π.left i) := by
      rw [NNReal.dist_eq, NNReal.dist_eq,
        abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hi.1.le)),
        abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast (_root_.Prove2MeSourceProof.h_fc4a2bac5634cdbfe2b154e5 π) i))]
      exact sub_le_sub_right (by exact_mod_cast hi.2) _
    _ = (π.gap i : ℝ) := (_root_.Prove2MeSourceProof.h_eaa152490266b02f7461a510 π) i
    _ ≤ π.mesh := by exact_mod_cast (_root_.Prove2MeSourceProof.h_62c96c8989b32380830efb77 π) i
end StochLean.TimePartition


