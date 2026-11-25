-- Prove2me | Definitions.Def_SourceProof_e0591ffe772e5ca30a6f7079
-- name    : SourceProof_e0591ffe772e5ca30a6f7079
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:06:45.571209+00:00
-- url     : https://prove2.me/theorems/c931b5be-7176-4459-99d4-6e5850c88599
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.jumpProcess_add

import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
import Definitions.Def_SourceProof_f91e26c2dc2e6815aedbe1f7
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Monoid

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Addition of source left limits and jumps, including time zero -/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {X Y : ℝ≥0 → Ω → ℝ} {ω : Ω}

namespace IsCadlagPath
theorem _root_.Prove2MeSourceProof.h_e0591ffe772e5ca30a6f7079 (hX : IsCadlagPath (X · ω))
    (hY : IsCadlagPath (Y · ω)) (t : ℝ≥0) :
    jumpProcess (X + Y) t ω = jumpProcess X t ω + jumpProcess Y t ω := by
  simp only [ProbabilityTheory.jumpProcess, Pi.sub_apply, Pi.add_apply, (_root_.Prove2MeSourceProof.h_f91e26c2dc2e6815aedbe1f7 hX) hY t]
  ring
end IsCadlagPath

end ProbabilityTheory


