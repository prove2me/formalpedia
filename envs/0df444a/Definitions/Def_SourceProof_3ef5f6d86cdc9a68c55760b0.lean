-- Prove2me | Definitions.Def_SourceProof_3ef5f6d86cdc9a68c55760b0
-- name    : SourceProof_3ef5f6d86cdc9a68c55760b0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:15:06.380104+00:00
-- url     : https://prove2.me/theorems/60c9001e-f858-44b8-ba78-299ab9a2349a
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.elementaryIntegralProcess_eq_elementaryIntegral_stopped

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F001
import Definitions.Def_SourceProof_1557efb7e848f4cf57c0170c
import Definitions.Def_SourceProof_9127ba9e47e57c570411dae8
import Definitions.Def_SourceProof_96c0d23ed76988d7c3d3ef45
import Definitions.Def_SourceProof_a239f509638bc9274841d0b5

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The source elementary integral process

Protter's `J_X(H)` is the existing elementary integral evaluated against `X` stopped
at the current deterministic time. This is not another general stochastic integral.
The source initial term is retained, including at time zero.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

namespace SimplePredictableRep

end SimplePredictableRep

namespace IsSimplePredictable

variable {H K : ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_3ef5f6d86cdc9a68c55760b0
    (hH : IsSimplePredictable H F) (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) :
    hH.elementaryIntegralProcess X t =
      hH.elementaryIntegral (stoppedProcess X (fun _ ↦ (t : WithTop ℝ≥0))) := by
  rfl
end IsSimplePredictable
end ProbabilityTheory


