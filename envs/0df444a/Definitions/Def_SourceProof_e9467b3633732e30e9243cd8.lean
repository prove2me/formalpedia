-- Prove2me | Definitions.Def_SourceProof_e9467b3633732e30e9243cd8
-- name    : SourceProof_e9467b3633732e30e9243cd8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:15:35.911689+00:00
-- url     : https://prove2.me/theorems/77f93342-7455-4c26-bb64-73c1d902a60f
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.discreteCoefficient_zero

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Sampling_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The elementary integral as an existing discrete predictable integral

The coefficient at index `n + 1` is measurable at the original left stopping endpoint, even
when the integrator is stopped at a deterministic horizon. No deterministic bound on the
partition endpoints, or change to their sigma-fields, is imposed.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal ENNReal BigOperators

namespace ProbabilityTheory.SimplePredictableRep

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

@[simp] theorem _root_.Prove2MeSourceProof.h_e9467b3633732e30e9243cd8 (H : SimplePredictableRep F) :
    H.discreteCoefficient 0 = 0 := rfl
end ProbabilityTheory.SimplePredictableRep


