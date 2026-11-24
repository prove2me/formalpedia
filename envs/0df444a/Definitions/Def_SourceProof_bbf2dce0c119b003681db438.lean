-- Prove2me | Definitions.Def_SourceProof_bbf2dce0c119b003681db438
-- name    : SourceProof_bbf2dce0c119b003681db438
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:14:54.486165+00:00
-- url     : https://prove2.me/theorems/e47b2e3b-a704-4752-bc8c-470b83efd60b
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.toProcess_zeroRep

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

@[simp] theorem _root_.Prove2MeSourceProof.h_bbf2dce0c119b003681db438 (F : Filtration ℝ≥0 mΩ) :
    (zero F).toProcess = 0 := by
  funext t ω
  by_cases ht : t = 0 <;>
    simp [ProbabilityTheory.SimplePredictableRep.toProcess, ProbabilityTheory.SimplePredictableRep.zero, StoppingTimePartition.deterministic, StochLean.TimePartition.empty, ht]
  all_goals exact Finset.sum_eq_zero (fun i _ => Fin.elim0 i)
end SimplePredictableRep

namespace IsSimplePredictable

variable {F : Filtration ℝ≥0 mΩ} {H : ℝ≥0 → Ω → ℝ}

end IsSimplePredictable
end ProbabilityTheory


