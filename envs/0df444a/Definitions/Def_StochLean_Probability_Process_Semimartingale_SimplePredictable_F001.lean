-- Prove2me | Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F001
-- name    : StochLean_Probability_Process_Semimartingale_SimplePredictable_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:56:59.436776+00:00
-- url     : https://prove2.me/theorems/17ad9cb5-0e9f-4f84-b547-006f66cdc4bf
-- title:
--   StochLean: Probability.Process.Semimartingale.SimplePredictable F001

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

def zero (F : Filtration ℝ≥0 mΩ) : SimplePredictableRep F where
  partition := StoppingTimePartition.deterministic F StochLean.TimePartition.empty
  initial := fun _ ↦ 0
  measurable_initial := measurable_const
  coefficient := Fin.elim0
  measurable_coefficient := fun i ↦ Fin.elim0 i
end SimplePredictableRep

namespace IsSimplePredictable

variable {F : Filtration ℝ≥0 mΩ} {H : ℝ≥0 → Ω → ℝ}

end IsSimplePredictable
end ProbabilityTheory


