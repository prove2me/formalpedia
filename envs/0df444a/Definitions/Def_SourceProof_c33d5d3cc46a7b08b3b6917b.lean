-- Prove2me | Definitions.Def_SourceProof_c33d5d3cc46a7b08b3b6917b
-- name    : SourceProof_c33d5d3cc46a7b08b3b6917b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:36:22.09677+00:00
-- url     : https://prove2.me/theorems/8e9eedcc-29da-5b98-b38d-afe938ddf57c
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.elementaryIntegral_stoppedFinite_eq_elementaryIntegralProcess

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F001
import Definitions.Def_SourceProof_1557efb7e848f4cf57c0170c
import Definitions.Def_SourceProof_66e575b29ed1f51be78afafb
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

theorem _root_.Prove2MeSourceProof.h_c33d5d3cc46a7b08b3b6917b
    (hH : IsSimplePredictable H F) (X : ℝ≥0 → Ω → ℝ) (τ : FiniteStoppingTime F) (ω : Ω) :
    hH.elementaryIntegral (stoppedProcess X τ.withTop) ω =
      hH.elementaryIntegralProcess X (τ ω) ω :=
  (_root_.Prove2MeSourceProof.h_66e575b29ed1f51be78afafb hH.choose) X τ ω
end IsSimplePredictable
end ProbabilityTheory


