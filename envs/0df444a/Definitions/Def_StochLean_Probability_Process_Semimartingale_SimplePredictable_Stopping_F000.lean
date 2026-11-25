-- Prove2me | Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Stopping_F000
-- name    : StochLean_Probability_Process_Semimartingale_SimplePredictable_Stopping_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:45:45.00201+00:00
-- url     : https://prove2.me/theorems/c3fafba0-98db-4c14-b139-65286e020504
-- title:
--   StochLean: Probability.Process.Semimartingale.SimplePredictable.Stopping F000

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Refinement_F000
import Definitions.Def_StochLean_Probability_Process_Stopping_Integrand_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Stopping the full source simple predictable class

The cutoff is `H 1_[0,τ]`, not the frozen stopped process `H^τ`. The source initial
coefficient is retained, including when the stopping time is zero. No boundedness
of coefficients or deterministic bound on the finite partition endpoints is imposed.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

namespace SimplePredictableRep

/-- Cut off on a common partition containing the finite stopping endpoint. -/
noncomputable def cutoffFinite (H : SimplePredictableRep F) (σ : FiniteStoppingTime F) :
    SimplePredictableRep F :=
  let ρ := H.partition.splitAt σ
  let R := H.repartition ρ
  { partition := ρ
    initial := H.initial
    measurable_initial := H.measurable_initial
    coefficient := fun i ω ↦ if ρ.point i.castSucc ω < σ ω then R.coefficient i ω else 0
    measurable_coefficient := fun i ↦ by
      have hs : MeasurableSet[(ρ.point i.castSucc).measurableSpace]
          {ω | ρ.point i.castSucc ω < σ ω} := by
        simpa only [Set.compl_ofPred, WithTop.coe_le_coe, not_le] using
          (σ.isStoppingTime.measurableSet_stopping_time_le
            (ρ.point i.castSucc).isStoppingTime).compl
      exact Measurable.ite hs (R.measurable_coefficient i) measurable_const }
end SimplePredictableRep

namespace IsSimplePredictable

variable {H : ℝ≥0 → Ω → ℝ}

end IsSimplePredictable
end ProbabilityTheory


