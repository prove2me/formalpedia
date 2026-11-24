-- Prove2me | Definitions.Def_SourceProof_f3db01ce3d4c266614f122be
-- name    : SourceProof_f3db01ce3d4c266614f122be
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:58:25.023599+00:00
-- url     : https://prove2.me/theorems/96749275-c585-4fd7-800c-8a77dc74f7ef
-- title:
--   StochLean source theorem: ProbabilityTheory.CompoundPoisson.measurable_convPow

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_Basic_F000
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

theorem _root_.Prove2MeSourceProof.h_f3db01ce3d4c266614f122be (μ : ProbabilityMeasure G) :
    Measurable (fun n : ℕ ↦ (ProbabilityMeasure.convPow μ n : Measure G)) :=
  measurable_of_countable _
section CharacteristicFunction

end CharacteristicFunction

end CompoundPoisson

end ProbabilityTheory


