-- Prove2me | Definitions.Def_SourceProof_d3a0db6a5b3b033e8d4b03a2
-- name    : SourceProof_d3a0db6a5b3b033e8d4b03a2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:44:55.10855+00:00
-- url     : https://prove2.me/theorems/397a76a0-a4c6-4580-97bd-190ef54274da
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCagladPath.exists_norm_bound_Icc

import Definitions.Def_StochLean_Probability_Process_Path_Caglad_F000
import Definitions.Def_SourceProof_73fd652f96ace405ff62d22b
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.Compactness.Compact

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Local and compact bounds for caglad paths

Left continuity and finite right limits jointly give an ordinary neighborhood
bound, including at time zero. A compact subcover gives the finite-horizon bound.
-/

@[expose] public section

open Set Filter
open scoped NNReal Topology

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] {x : ℝ≥0 → E}

namespace IsCagladPath
theorem _root_.Prove2MeSourceProof.h_d3a0db6a5b3b033e8d4b03a2 (hx : IsCagladPath x) (T : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc 0 T, ‖x t‖ ≤ C :=
  (_root_.Prove2MeSourceProof.h_73fd652f96ace405ff62d22b hx) isCompact_Icc
end IsCagladPath

end ProbabilityTheory


