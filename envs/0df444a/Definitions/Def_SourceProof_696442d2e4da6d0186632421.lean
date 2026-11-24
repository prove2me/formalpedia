-- Prove2me | Definitions.Def_SourceProof_696442d2e4da6d0186632421
-- name    : SourceProof_696442d2e4da6d0186632421
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:14:31.166363+00:00
-- url     : https://prove2.me/theorems/0c0758d5-432b-48b3-8753-84539327e78f
-- title:
--   StochLean source theorem: ProbabilityTheory.CompoundPoisson.ofFiniteMeasure_zero

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_CompoundPoisson_F001

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

section CharacteristicFunction

end CharacteristicFunction

@[simp]
theorem _root_.Prove2MeSourceProof.h_696442d2e4da6d0186632421 :
    ofFiniteMeasure (0 : FiniteMeasure G) = ProbabilityMeasure.pointMass (G := G) 0 := by
  simp [ProbabilityTheory.CompoundPoisson.ofFiniteMeasure]
end CompoundPoisson

end ProbabilityTheory


