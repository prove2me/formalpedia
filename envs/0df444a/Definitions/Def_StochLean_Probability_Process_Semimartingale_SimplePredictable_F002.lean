-- Prove2me | Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F002
-- name    : StochLean_Probability_Process_Semimartingale_SimplePredictable_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:57:16.557488+00:00
-- url     : https://prove2.me/theorems/ccc45082-53b8-4c75-86dc-8df0556d1b1b
-- title:
--   StochLean: Probability.Process.Semimartingale.SimplePredictable F002

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

/-- A deterministic source interval with separate time-zero and positive-time coefficients. -/
def deterministicInterval (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (a c : ℝ) :
    SimplePredictableRep F where
  partition := StoppingTimePartition.deterministic F (StochLean.TimePartition.single T)
  initial := fun _ ↦ a
  measurable_initial := measurable_const
  coefficient := fun _ _ ↦ c
  measurable_coefficient := fun _ ↦ measurable_const
end SimplePredictableRep

namespace IsSimplePredictable

variable {F : Filtration ℝ≥0 mΩ} {H : ℝ≥0 → Ω → ℝ}

end IsSimplePredictable
end ProbabilityTheory


