-- Prove2me | Definitions.Def_SourceProof_31206da94e8ad4f6bba4c1fa
-- name    : SourceProof_31206da94e8ad4f6bba4c1fa
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:02:14.400844+00:00
-- url     : https://prove2.me/theorems/f31098fc-98c3-4b5f-a9c3-3cde6a3189e7
-- title:
--   StochLean source theorem: StochLean.TimePartition.dist_ceilingPoint_le_mesh

import Definitions.Def_SourceProof_41c8e0f72444e5cb2bd104fc
import Definitions.Def_SourceProof_62c96c8989b32380830efb77
import Definitions.Def_SourceProof_d90de18cdaae59a2bf0af35c
import Definitions.Def_SourceProof_eaa152490266b02f7461a510

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Endpoint approximations for finite partitions

The right endpoint projection is monotone, remains in the original endpoint
set, and is at distance at most the mesh on the compact horizon. This is a
deterministic approximation: no extra grid is inserted.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace StochLean.TimePartition

variable {T : ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_31206da94e8ad4f6bba4c1fa (π : TimePartition T) {t : ℝ≥0} (ht : t ≤ T) :
    dist (π.ceilingPoint t) t ≤ (π.mesh : ℝ) := by
  have htc : t ≤ (StochLean.TimePartition.ceilingPoint π) t := by simpa [min_eq_left ht] using (_root_.Prove2MeSourceProof.h_41c8e0f72444e5cb2bd104fc π) t
  by_cases hzero : π.ceilingIndex t = 0
  · have hc : (StochLean.TimePartition.ceilingPoint π) t = 0 := by simp [StochLean.TimePartition.ceilingPoint, hzero, π.first_eq_zero]
    have ht0 : t = 0 := le_antisymm (htc.trans_eq hc) bot_le
    rw [hc, ht0, dist_self]
    exact NNReal.coe_nonneg _
  · let i : Fin π.size := (π.ceilingIndex t).pred hzero
    have hir : (StochLean.TimePartition.right π) i = (StochLean.TimePartition.ceilingPoint π) t := by simp [StochLean.TimePartition.right, i, StochLean.TimePartition.ceilingPoint]
    have hil : π.left i < t := by
      apply lt_of_not_ge
      intro hle
      have hmin := (_root_.Prove2MeSourceProof.h_d90de18cdaae59a2bf0af35c (i := i.castSucc) π) ((min_le_left t T).trans hle)
      have hlt : i.castSucc < π.ceilingIndex t := by
        simpa [i] using (Fin.castSucc_lt_succ (i := i))
      exact (not_le_of_gt hlt) hmin
    calc
      dist ((StochLean.TimePartition.ceilingPoint π) t) t ≤ dist ((StochLean.TimePartition.right π) i) (π.left i) := by
        rw [hir, NNReal.dist_eq, NNReal.dist_eq,
          abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast htc)),
          abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast (hil.le.trans htc)))]
        exact sub_le_sub_left (by exact_mod_cast hil.le) _
      _ = (π.gap i : ℝ) := (_root_.Prove2MeSourceProof.h_eaa152490266b02f7461a510 π) i
      _ ≤ π.mesh := by exact_mod_cast (_root_.Prove2MeSourceProof.h_62c96c8989b32380830efb77 π) i
end StochLean.TimePartition


