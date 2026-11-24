-- Prove2me | Definitions.Def_StochLean_Probability_Process_Path_Continuous_F000
-- name    : StochLean_Probability_Process_Path_Continuous_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:46:22.922387+00:00
-- url     : https://prove2.me/theorems/d9988fbc-288e-4cff-bf4f-79a220fe6e38
-- title:
--   StochLean: Probability.Process.Path.Continuous F000

import Definitions.Def_StochLean_Probability_Process_Path_RightContinuous_F000

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

def IsContinuousPath (x : T → E) : Prop :=
  Continuous x
def HasContinuousPaths (X : T → Ω → E) (P : Measure Ω := by volume_tac) : Prop :=
  ∀ᵐ ω ∂P, IsContinuousPath fun t ↦ X t ω
namespace HasContinuousPaths

variable {X Y : T → Ω → E} {P : Measure Ω}

end HasContinuousPaths

namespace IsContinuousPath

variable [Preorder T]

end IsContinuousPath

end ProbabilityTheory


