-- Prove2me | Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F003
-- name    : StochLean_Probability_Process_Semimartingale_SimplePredictable_F003
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:57:12.02827+00:00
-- url     : https://prove2.me/theorems/b97f7352-a0f1-469e-aaab-6c401722220b
-- title:
--   StochLean: Probability.Process.Semimartingale.SimplePredictable F003

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

end SimplePredictableRep

/-- The source simple predictable class as an extensional predicate on raw processes. -/
def IsSimplePredictable (H : ℝ≥0 → Ω → ℝ) (F : Filtration ℝ≥0 mΩ) : Prop :=
  ∃ R : SimplePredictableRep F, R.toProcess = H
namespace IsSimplePredictable

variable {F : Filtration ℝ≥0 mΩ} {H : ℝ≥0 → Ω → ℝ}

/-- The source elementary integral. Choice is independent of the representation by
`SimplePredictableRep.integral_congr`. It is available only for a simple predictable integrand. -/
noncomputable def elementaryIntegral (hH : IsSimplePredictable H F)
    (X : ℝ≥0 → Ω → ℝ) : Ω → ℝ := hH.choose.integral X
end IsSimplePredictable
end ProbabilityTheory


