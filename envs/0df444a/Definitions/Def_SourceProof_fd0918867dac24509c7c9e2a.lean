-- Prove2me | Definitions.Def_SourceProof_fd0918867dac24509c7c9e2a
-- name    : SourceProof_fd0918867dac24509c7c9e2a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:01:50.332345+00:00
-- url     : https://prove2.me/theorems/f3f232fb-daa8-4da7-ac67-e0255b088cb4
-- title:
--   StochLean source theorem: ProbabilityTheory.IsContinuousPath.isLeftContinuousPath

import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Almost-sure left-continuous and càdlàg paths

This file provides only trajectory predicates. It does not construct the Skorokhod topology.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω}

section LeftContinuous

variable [Preorder T] [TopologicalSpace T] [TopologicalSpace E]

namespace HasLeftContinuousPaths

variable {X Y : T → Ω → E} {P : Measure Ω}

end HasLeftContinuousPaths

namespace IsContinuousPath

theorem _root_.Prove2MeSourceProof.h_fd0918867dac24509c7c9e2a {x : T → E} (h : IsContinuousPath x) :
    IsLeftContinuousPath x :=
  fun _ ↦ h.continuousWithinAt
end IsContinuousPath

end LeftContinuous

section Cadlag

variable [LinearOrder T] [TopologicalSpace T] [OrderBot T]
  [TopologicalSpace E]

namespace HasCadlagPaths

variable {X Y : T → Ω → E} {P : Measure Ω}

end HasCadlagPaths

end Cadlag

end ProbabilityTheory


