-- Prove2me | Definitions.Def_StochLean_Probability_InfinitelyDivisible_CompoundPoisson_F000
-- name    : StochLean_Probability_InfinitelyDivisible_CompoundPoisson_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:07:43.75285+00:00
-- url     : https://prove2.me/theorems/a7c39e7a-17af-47e8-8a5d-fa52ba1e1718
-- title:
--   StochLean: Probability.InfinitelyDivisible.CompoundPoisson F000

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_Basic_F000
import Definitions.Def_SourceProof_f3db01ce3d4c266614f122be
import Mathlib.Probability.Distributions.Poisson.Basic

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Compound Poisson laws

The construction is a genuine probability mixture: draw a Poisson count and then use the
corresponding convolution power of the jump law.  The zero-rate branch is proved explicitly and
does not depend on division by the intensity.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

namespace CompoundPoisson

variable {G : Type*} [AddCommMonoid G] [MeasurableSpace G] [MeasurableAdd₂ G]

/-- The compound Poisson law of intensity `r` and jump law `μ`. -/
noncomputable def law (r : ℝ≥0) (μ : ProbabilityMeasure G) : ProbabilityMeasure G := by
  let f : ℕ → Measure G := fun n ↦ ProbabilityMeasure.convPow μ n
  refine ⟨(poissonMeasure r).bind f, ?_⟩
  apply isProbabilityMeasure_bind (_root_.Prove2MeSourceProof.h_f3db01ce3d4c266614f122be μ).aemeasurable
  exact ae_of_all _ fun n ↦ inferInstance
section CharacteristicFunction

end CharacteristicFunction

end CompoundPoisson

end ProbabilityTheory


