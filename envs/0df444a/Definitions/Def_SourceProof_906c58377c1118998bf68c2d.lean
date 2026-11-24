-- Prove2me | Definitions.Def_SourceProof_906c58377c1118998bf68c2d
-- name    : SourceProof_906c58377c1118998bf68c2d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:46:01.806475+00:00
-- url     : https://prove2.me/theorems/b0a57884-a2aa-4822-94f8-a2712bd3bb85
-- title:
--   StochLean source theorem: StochLean.TimePartition.abs_increment_le_maxIncrement

import Definitions.Def_StochLean_Analysis_PathVariation_Oscillation_F000

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

theorem _root_.Prove2MeSourceProof.h_906c58377c1118998bf68c2d (π : TimePartition T) (f : ℝ≥0 → ℝ)
    (i : Fin π.size) : |π.increment f i| ≤ (π.maxIncrement f : ℝ) := by
  exact_mod_cast (Finset.le_sup (f := fun i ↦ ‖π.increment f i‖₊) (Finset.mem_univ i))
end StochLean.TimePartition


