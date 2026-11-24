-- Prove2me | Definitions.Def_SourceProof_2c0d4ca99a3f51a9d8eb6cb0
-- name    : SourceProof_2c0d4ca99a3f51a9d8eb6cb0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:15:28.217271+00:00
-- url     : https://prove2.me/theorems/7e930cb1-0328-4e24-88c5-77894eae595e
-- title:
--   StochLean source theorem: ProbabilityTheory.HasContinuousPaths.hasCadlagPaths

import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
import Definitions.Def_SourceProof_a2cb63993a652b5632791121

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

namespace HasContinuousPaths
theorem _root_.Prove2MeSourceProof.h_2c0d4ca99a3f51a9d8eb6cb0 {X : T → Ω → E} {P : Measure Ω}
    (hx : HasContinuousPaths X P) : HasCadlagPaths X P :=
  hx.mono fun _ hω ↦ (_root_.Prove2MeSourceProof.h_a2cb63993a652b5632791121 hω)
end HasContinuousPaths

namespace HasCadlagPaths

variable {X Y : T → Ω → E} {P : Measure Ω}

end HasCadlagPaths

end Cadlag

end ProbabilityTheory


