-- Prove2me | Definitions.Def_SourceProof_ffe0bffb5a465ffb7d0925ec
-- name    : SourceProof_ffe0bffb5a465ffb7d0925ec
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:02:04.742626+00:00
-- url     : https://prove2.me/theorems/7daf61ac-3fd1-42ba-b37b-a69afb3c3aa6
-- title:
--   StochLean source theorem: StochLean.TimePartition.le_ceilingPoint_iff_of_mem_cell

import Definitions.Def_SourceProof_5b01082e74980c6a3919e38a

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Sampling a right-continuous interval step moves its endpoints upwards

Ceilings use the original partition points and are capped at its horizon.
Repeated endpoints are allowed. The increment identity is valid for every
integrator, before any right-continuity or semimartingale assumption.
-/

@[expose] public section

open Filter Set Finset
open scoped NNReal Topology

namespace StochLean.TimePartition

variable {T : ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_ffe0bffb5a465ffb7d0925ec (π : TimePartition T) {t : ℝ≥0}
    {i : Fin π.size} (hi : π.left i < t ∧ t ≤ π.right i) (a : ℝ≥0) :
    t ≤ π.ceilingPoint a ↔ π.left i < a := by
  simpa only [not_lt, not_le] using not_congr ((_root_.Prove2MeSourceProof.h_5b01082e74980c6a3919e38a π) hi a)
end StochLean.TimePartition


