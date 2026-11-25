-- Prove2me | Definitions.Def_SourceProof_08d1413f21e139fa3b976ce1
-- name    : SourceProof_08d1413f21e139fa3b976ce1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:34:08.216361+00:00
-- url     : https://prove2.me/theorems/7803d247-d276-485c-9daa-2498df0c8f86
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.exists_norm_bound_Icc

import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F000
import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
import Definitions.Def_SourceProof_b5697f710fe6829a60e25fdb
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.Compactness.Compact

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Local and compact bounds for cadlag paths

The lower endpoint is treated by right continuity alone. At positive times,
the actual finite left limit and right continuity give a neighborhood bound.
-/

@[expose] public section

open Set Filter
open scoped NNReal Topology

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] {x : ℝ≥0 → E}

namespace IsCadlagPath
theorem _root_.Prove2MeSourceProof.h_08d1413f21e139fa3b976ce1 (hx : IsCadlagPath x) (T : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc 0 T, ‖x t‖ ≤ C :=
  (_root_.Prove2MeSourceProof.h_b5697f710fe6829a60e25fdb hx) isCompact_Icc
end IsCadlagPath

end ProbabilityTheory


