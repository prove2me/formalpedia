-- Prove2me | Definitions.Def_SourceProof_a2f6eccafa4fd5a29354c02c
-- name    : SourceProof_a2f6eccafa4fd5a29354c02c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:37:58.065138+00:00
-- url     : https://prove2.me/theorems/e3a8c75d-ebe8-5a53-b37d-e13fbdbff4a1
-- title:
--   StochLean source theorem: ProbabilityTheory.HasContinuousPaths.congr

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

theorem _root_.Prove2MeSourceProof.h_a2f6eccafa4fd5a29354c02c (hXY : Indistinguishable X Y P) (hX : HasContinuousPaths X P) :
    HasContinuousPaths Y P := by
  filter_upwards [hXY, hX] with ω hω hcont
  simpa only [ProbabilityTheory.IsContinuousPath, hω] using hcont
end HasContinuousPaths

namespace IsContinuousPath

variable [Preorder T]

end IsContinuousPath

end ProbabilityTheory


