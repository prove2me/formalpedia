-- Prove2me | Definitions.Def_SourceProof_9f2f3563711c68b81e63664c
-- name    : SourceProof_9f2f3563711c68b81e63664c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:06:51.122257+00:00
-- url     : https://prove2.me/theorems/9a2257f8-1611-40b5-b983-c274ff939661
-- title:
--   StochLean source theorem: ProbabilityTheory.HasCadlagPaths.hasRightContinuousPaths

import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001

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

namespace HasCadlagPaths

variable {X Y : T → Ω → E} {P : Measure Ω}

theorem _root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c (h : HasCadlagPaths X P) : HasRightContinuousPaths X P :=
  h.mono fun _ hω ↦ hω.1
end HasCadlagPaths

end Cadlag

end ProbabilityTheory


