-- Prove2me | Definitions.Def_SourceProof_8db4335308fcb07f2558487f
-- name    : SourceProof_8db4335308fcb07f2558487f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:46:00.639151+00:00
-- url     : https://prove2.me/theorems/343a955d-686a-4d30-829a-3462f283a55f
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.discreteCoefficient_fin

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

theorem _root_.Prove2MeSourceProof.h_8db4335308fcb07f2558487f (H : SimplePredictableRep F) (i : Fin H.partition.size) :
    H.discreteCoefficient (i + 1) = H.coefficient i := by
  simp only [ProbabilityTheory.SimplePredictableRep.discreteCoefficient, dif_pos i.isLt]
end ProbabilityTheory.SimplePredictableRep


