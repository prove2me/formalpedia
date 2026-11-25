-- Prove2me | Definitions.Def_SourceProof_f354c3aa1b2bfac52fcde7e4
-- name    : SourceProof_f354c3aa1b2bfac52fcde7e4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:51:31.657186+00:00
-- url     : https://prove2.me/theorems/0e9a89ee-62b7-5a69-aa8e-4a1b518f78ba
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.integral_zero

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F001

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

@[simp] theorem _root_.Prove2MeSourceProof.h_f354c3aa1b2bfac52fcde7e4 (F : Filtration ℝ≥0 mΩ) (X : ℝ≥0 → Ω → ℝ) :
    (zero F).integral X = 0 := by
  funext ω
  simp [ProbabilityTheory.SimplePredictableRep.integral, ProbabilityTheory.SimplePredictableRep.zero, StoppingTimePartition.deterministic, StochLean.TimePartition.empty]
end SimplePredictableRep

namespace IsSimplePredictable

variable {F : Filtration ℝ≥0 mΩ} {H : ℝ≥0 → Ω → ℝ}

end IsSimplePredictable
end ProbabilityTheory


