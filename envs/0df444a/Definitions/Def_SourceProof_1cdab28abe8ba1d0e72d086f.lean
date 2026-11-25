-- Prove2me | Definitions.Def_SourceProof_1cdab28abe8ba1d0e72d086f
-- name    : SourceProof_1cdab28abe8ba1d0e72d086f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:13:33.418702+00:00
-- url     : https://prove2.me/theorems/1096baa4-1dce-5d16-a4f4-f6173179d02a
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.jumpProcess_sub

import Definitions.Def_SourceProof_264d677d5da3fcd447059c80
import Definitions.Def_SourceProof_cdca0fcca64ca77da16e2981
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
theorem _root_.Prove2MeSourceProof.h_1cdab28abe8ba1d0e72d086f (hX : IsCadlagPath (X · ω))
    (hY : IsCadlagPath (Y · ω)) (t : ℝ≥0) :
    jumpProcess (X - Y) t ω = jumpProcess X t ω - jumpProcess Y t ω := by
  simp only [ProbabilityTheory.jumpProcess, Pi.sub_apply, (_root_.Prove2MeSourceProof.h_cdca0fcca64ca77da16e2981 hX) hY t]
  ring
end IsCadlagPath

end ProbabilityTheory


