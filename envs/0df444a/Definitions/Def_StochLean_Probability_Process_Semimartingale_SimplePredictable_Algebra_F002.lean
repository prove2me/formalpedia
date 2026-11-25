-- Prove2me | Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Algebra_F002
-- name    : StochLean_Probability_Process_Semimartingale_SimplePredictable_Algebra_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:45:01.393301+00:00
-- url     : https://prove2.me/theorems/d8cd6809-521b-4290-8624-28d222db2ddf
-- title:
--   StochLean: Probability.Process.Semimartingale.SimplePredictable.Algebra F002

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Refinement_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Algebra of the full source simple predictable class

The operations use actual common stopping-time refinements. Coefficients remain arbitrary
finite random variables, measurable at their left endpoints. Binary Borel operations fixing
`(0, 0)` preserve the class; in particular it is closed under addition and multiplication.
The elementary integral is bilinear, with its source initial term retained.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

namespace SimplePredictableRep

/-- Scalar multiplication does not require a new stopping partition. -/
def scale (H : SimplePredictableRep F) (c : ℝ) : SimplePredictableRep F where
  partition := H.partition
  initial := fun ω ↦ c * H.initial ω
  measurable_initial := measurable_const.mul H.measurable_initial
  coefficient := fun i ω ↦ c * H.coefficient i ω
  measurable_coefficient := fun i ↦ measurable_const.mul (H.measurable_coefficient i)
end SimplePredictableRep

namespace IsSimplePredictable

variable {H K : ℝ≥0 → Ω → ℝ}

end IsSimplePredictable
end ProbabilityTheory


