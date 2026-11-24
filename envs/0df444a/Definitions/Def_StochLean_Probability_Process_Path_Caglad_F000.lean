-- Prove2me | Definitions.Def_StochLean_Probability_Process_Path_Caglad_F000
-- name    : StochLean_Probability_Process_Path_Caglad_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:06:53.349616+00:00
-- url     : https://prove2.me/theorems/ebab79fc-b7b3-4284-aa46-f85b536d76c4
-- title:
--   StochLean: Probability.Process.Path.Caglad F000

import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F000
import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001

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

def IsCagladPath (x : T → E) : Prop :=
  IsLeftContinuousPath x ∧ ∀ t, ∃ y : E, Tendsto x (nhdsWithin t (Ioi t)) (𝓝 y)
def HasCagladPaths (X : T → Ω → E) (P : Measure Ω := by volume_tac) : Prop :=
  ∀ᵐ ω ∂P, IsCagladPath fun t ↦ X t ω
end ProbabilityTheory


