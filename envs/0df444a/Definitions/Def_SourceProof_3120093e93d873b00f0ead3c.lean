-- Prove2me | Definitions.Def_SourceProof_3120093e93d873b00f0ead3c
-- name    : SourceProof_3120093e93d873b00f0ead3c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:02:28.938688+00:00
-- url     : https://prove2.me/theorems/15f72bf2-f7d0-4997-8ff5-0e9c51116084
-- title:
--   StochLean source theorem: ProbabilityTheory.CompoundPoisson.ofFiniteMeasure_eq_of_ne_zero

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

theorem _root_.Prove2MeSourceProof.h_3120093e93d873b00f0ead3c {ν : FiniteMeasure G} (hν : ν ≠ 0) :
    ofFiniteMeasure ν = law ν.mass ν.normalize := by
  simp [ProbabilityTheory.CompoundPoisson.ofFiniteMeasure, hν]
end CompoundPoisson

end ProbabilityTheory


