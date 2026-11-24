-- Prove2me | Definitions.Def_SourceProof_a2cb63993a652b5632791121
-- name    : SourceProof_a2cb63993a652b5632791121
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:07:07.724948+00:00
-- url     : https://prove2.me/theorems/f1345f77-846a-4bc7-a1b4-00b9bd95d83c
-- title:
--   StochLean source theorem: ProbabilityTheory.IsContinuousPath.isCadlagPath

import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
import Definitions.Def_SourceProof_245119f42083b7c11a8dd571

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

end IsContinuousPath

end LeftContinuous

section Cadlag

variable [LinearOrder T] [TopologicalSpace T] [OrderBot T]
  [TopologicalSpace E]

namespace IsContinuousPath
theorem _root_.Prove2MeSourceProof.h_a2cb63993a652b5632791121 {x : T → E} (hx : IsContinuousPath x) :
    IsCadlagPath x :=
  ⟨(_root_.Prove2MeSourceProof.h_245119f42083b7c11a8dd571 hx), fun t _ ↦ ⟨x t, hx.continuousAt.continuousWithinAt⟩⟩
end IsContinuousPath

namespace HasCadlagPaths

variable {X Y : T → Ω → E} {P : Measure Ω}

end HasCadlagPaths

end Cadlag

end ProbabilityTheory


