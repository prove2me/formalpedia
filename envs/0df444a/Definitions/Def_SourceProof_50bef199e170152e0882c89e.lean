-- Prove2me | Definitions.Def_SourceProof_50bef199e170152e0882c89e
-- name    : SourceProof_50bef199e170152e0882c89e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:10:02.7609+00:00
-- url     : https://prove2.me/theorems/348f9c20-78ef-4a2c-8002-e0b681177017
-- title:
--   StochLean source theorem: ProbabilityTheory.IsContinuousPath.isCagladPath

import Definitions.Def_StochLean_Probability_Process_Path_Caglad_F000
import Definitions.Def_SourceProof_fd0918867dac24509c7c9e2a

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Common-event càglàd paths

Chapter II integrands have left-continuous paths with finite right limits.
The existential right limit does not select a default outside this domain.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace ProbabilityTheory

variable {T Ω E : Type*} [LinearOrder T] [TopologicalSpace T]
  [TopologicalSpace E] {mΩ : MeasurableSpace Ω} {P : Measure Ω}

namespace IsContinuousPath
theorem _root_.Prove2MeSourceProof.h_50bef199e170152e0882c89e {x : T → E} (hx : IsContinuousPath x) :
    IsCagladPath x :=
  ⟨(_root_.Prove2MeSourceProof.h_fd0918867dac24509c7c9e2a hx), fun t ↦ ⟨x t, hx.continuousAt.continuousWithinAt⟩⟩
end IsContinuousPath

end ProbabilityTheory


