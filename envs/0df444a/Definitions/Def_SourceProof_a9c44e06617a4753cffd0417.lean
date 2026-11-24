-- Prove2me | Definitions.Def_SourceProof_a9c44e06617a4753cffd0417
-- name    : SourceProof_a9c44e06617a4753cffd0417
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:57:07.458507+00:00
-- url     : https://prove2.me/theorems/db62a4b5-2d24-4d13-ab44-7368b39483e1
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.toProcess_zero

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Protter simple predictable processes and their elementary integral

The coefficients are finite real random variables, measurable at the left
stopping endpoint. They need not be bounded. A representation is witness data;
the public process is a raw function. Representation independence is proved
before the public integral selector is introduced.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal BigOperators

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

namespace SimplePredictableRep

variable {F : Filtration ℝ≥0 mΩ}

@[simp] theorem _root_.Prove2MeSourceProof.h_a9c44e06617a4753cffd0417 (H : SimplePredictableRep F) (ω : Ω) :
    H.toProcess 0 ω = H.initial ω := by simp [ProbabilityTheory.SimplePredictableRep.toProcess]
end SimplePredictableRep

namespace IsSimplePredictable

variable {F : Filtration ℝ≥0 mΩ} {H : ℝ≥0 → Ω → ℝ}

end IsSimplePredictable
end ProbabilityTheory


