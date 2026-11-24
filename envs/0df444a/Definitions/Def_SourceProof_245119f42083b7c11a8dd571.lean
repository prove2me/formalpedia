-- Prove2me | Definitions.Def_SourceProof_245119f42083b7c11a8dd571
-- name    : SourceProof_245119f42083b7c11a8dd571
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:58:17.695805+00:00
-- url     : https://prove2.me/theorems/e4f39142-32a3-4c98-9ce1-8232ec812155
-- title:
--   StochLean source theorem: ProbabilityTheory.IsContinuousPath.isRightContinuousPath

import Definitions.Def_StochLean_Probability_Process_Path_Continuous_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Almost-sure continuous paths

Path properties use one common full-measure event for the whole trajectory.
-/

@[expose] public section

open MeasureTheory Filter

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω}
  [TopologicalSpace T] [TopologicalSpace E]

namespace HasContinuousPaths

variable {X Y : T → Ω → E} {P : Measure Ω}

end HasContinuousPaths

namespace IsContinuousPath

variable [Preorder T]

theorem _root_.Prove2MeSourceProof.h_245119f42083b7c11a8dd571 {x : T → E} (h : IsContinuousPath x) :
    IsRightContinuousPath x :=
  fun _ ↦ h.continuousWithinAt
end IsContinuousPath

end ProbabilityTheory


