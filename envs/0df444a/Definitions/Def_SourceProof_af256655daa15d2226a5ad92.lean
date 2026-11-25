-- Prove2me | Definitions.Def_SourceProof_af256655daa15d2226a5ad92
-- name    : SourceProof_af256655daa15d2226a5ad92
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:45:57.826131+00:00
-- url     : https://prove2.me/theorems/348cd177-dccf-414a-b642-80f85ce05dd1
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.jumpProcess_sq

import Definitions.Def_SourceProof_264d677d5da3fcd447059c80
import Definitions.Def_SourceProof_555fdf58cf2acc34e4941dfb
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Monoid

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Algebra of source left limits and jumps

Continuous scalar transformations must preserve zero to commute with the
source left limit at every time, including the special time-zero value.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X Y : ℝ≥0 → Ω → ℝ} {ω : Ω}

namespace IsCadlagPath
theorem _root_.Prove2MeSourceProof.h_af256655daa15d2226a5ad92 (hX : IsCadlagPath (X · ω)) (t : ℝ≥0) :
    jumpProcess (fun s v ↦ (X s v) ^ 2) t ω =
      (X t ω) ^ 2 - (leftLimitProcess X t ω) ^ 2 := by
  simp only [ProbabilityTheory.jumpProcess, Pi.sub_apply,
    (_root_.Prove2MeSourceProof.h_555fdf58cf2acc34e4941dfb (f := fun x ↦ x ^ 2) hX) (continuous_id.pow 2) (by norm_num) t]
end IsCadlagPath

end ProbabilityTheory


