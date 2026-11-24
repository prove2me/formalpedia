-- Prove2me | Definitions.Def_SourceProof_8f7895612117943074291d58
-- name    : SourceProof_8f7895612117943074291d58
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:00:23.808829+00:00
-- url     : https://prove2.me/theorems/69249a25-675f-4e88-a940-f1f0bac882a6
-- title:
--   StochLean source theorem: StochLean.TimePartition.exists_cell

import Definitions.Def_StochLean_Analysis_PathVariation_Approximation_F000
import Definitions.Def_SourceProof_41c8e0f72444e5cb2bd104fc
import Definitions.Def_SourceProof_d90de18cdaae59a2bf0af35c
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

theorem _root_.Prove2MeSourceProof.h_8f7895612117943074291d58 (π : TimePartition T) {t : ℝ≥0} (ht : t ∈ Ioc 0 T) :
    ∃ i : Fin π.size, π.left i < t ∧ t ≤ π.right i := by
  have htc : t ≤ (StochLean.TimePartition.ceilingPoint π) t := by
    simpa only [min_eq_left ht.2] using (_root_.Prove2MeSourceProof.h_41c8e0f72444e5cb2bd104fc π) t
  have hzero : π.ceilingIndex t ≠ 0 := by
    intro hz
    have hc : (StochLean.TimePartition.ceilingPoint π) t = 0 := by simp only [StochLean.TimePartition.ceilingPoint, hz, π.first_eq_zero]
    exact not_lt_of_ge (htc.trans_eq hc) ht.1
  let i : Fin π.size := (π.ceilingIndex t).pred hzero
  have hir : (StochLean.TimePartition.right π) i = (StochLean.TimePartition.ceilingPoint π) t := by simp [StochLean.TimePartition.right, i, StochLean.TimePartition.ceilingPoint]
  refine ⟨i, ?_, hir ▸ htc⟩
  apply lt_of_not_ge
  intro hle
  have hmin := (_root_.Prove2MeSourceProof.h_d90de18cdaae59a2bf0af35c (i := i.castSucc) π) ((min_le_left t T).trans hle)
  have hlt : i.castSucc < π.ceilingIndex t := by
    simpa [i] using (Fin.castSucc_lt_succ (i := i))
  exact (not_le_of_gt hlt) hmin
end StochLean.TimePartition


