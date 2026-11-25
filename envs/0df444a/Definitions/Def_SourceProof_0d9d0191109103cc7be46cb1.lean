-- Prove2me | Definitions.Def_SourceProof_0d9d0191109103cc7be46cb1
-- name    : SourceProof_0d9d0191109103cc7be46cb1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:43:54.531336+00:00
-- url     : https://prove2.me/theorems/51b8a409-d16e-5f1e-bb35-9406812abf32
-- title:
--   StochLean source theorem: StochLean.TimePartition.cell_unique

import Definitions.Def_StochLean_Analysis_PathVariation_Approximation_F000
import Definitions.Def_StochLean_Analysis_PathVariation_Approximation_F002
import Definitions.Def_SourceProof_bd0fe3b017a364f85ef29095
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

theorem _root_.Prove2MeSourceProof.h_0d9d0191109103cc7be46cb1 (π : TimePartition T) {t : ℝ≥0} {i j : Fin π.size}
    (hi : π.left i < t ∧ t ≤ π.right i) (hj : π.left j < t ∧ t ≤ π.right j) : i = j := by
  apply le_antisymm
  · apply le_of_not_gt
    intro hji
    exact not_lt_of_ge (hj.2.trans ((_root_.Prove2MeSourceProof.h_bd0fe3b017a364f85ef29095 π) hji)) hi.1
  · apply le_of_not_gt
    intro hij
    exact not_lt_of_ge (hi.2.trans ((_root_.Prove2MeSourceProof.h_bd0fe3b017a364f85ef29095 π) hij)) hj.1
end StochLean.TimePartition


