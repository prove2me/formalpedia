-- Prove2me | Definitions.Def_SourceProof_afa4a77c82348c083f81d8eb
-- name    : SourceProof_afa4a77c82348c083f81d8eb
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:15:16.804274+00:00
-- url     : https://prove2.me/theorems/0e67bb81-06dd-4b15-b54f-127501925b90
-- title:
--   StochLean source theorem: ProbabilityTheory.CompoundPoisson.coe_law

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_CompoundPoisson_F000

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

@[simp, norm_cast]
theorem _root_.Prove2MeSourceProof.h_afa4a77c82348c083f81d8eb (r : ℝ≥0) (μ : ProbabilityMeasure G) :
    ((law r μ : ProbabilityMeasure G) : Measure G) =
      (poissonMeasure r).bind (fun n ↦ ProbabilityMeasure.convPow μ n) :=
  rfl
section CharacteristicFunction

end CharacteristicFunction

end CompoundPoisson

end ProbabilityTheory


