-- Prove2me | Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Algebra_F000
-- name    : StochLean_Probability_Process_Semimartingale_SimplePredictable_Algebra_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:45:12.281962+00:00
-- url     : https://prove2.me/theorems/54f795b7-75f7-47e2-8b05-c1aac11f96b7
-- title:
--   StochLean: Probability.Process.Semimartingale.SimplePredictable.Algebra F000

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

/-- Combine the two repartitioned coefficient families on one proposed partition. -/
noncomputable def combineOn (H K : SimplePredictableRep F) (ρ : StoppingTimePartition F)
    (φ : ℝ → ℝ → ℝ) (hφ : Measurable (Function.uncurry φ)) : SimplePredictableRep F where
  partition := ρ
  initial := fun ω ↦ φ (H.initial ω) (K.initial ω)
  measurable_initial := hφ.comp (H.measurable_initial.prodMk K.measurable_initial)
  coefficient := fun i ω ↦ φ ((H.repartition ρ).coefficient i ω)
    ((K.repartition ρ).coefficient i ω)
  measurable_coefficient := fun i ↦ hφ.comp
    (((H.repartition ρ).measurable_coefficient i).prodMk
      ((K.repartition ρ).measurable_coefficient i))
end SimplePredictableRep

namespace IsSimplePredictable

variable {H K : ℝ≥0 → Ω → ℝ}

end IsSimplePredictable
end ProbabilityTheory


