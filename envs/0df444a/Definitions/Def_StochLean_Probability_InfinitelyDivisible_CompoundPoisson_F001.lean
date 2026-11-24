-- Prove2me | Definitions.Def_StochLean_Probability_InfinitelyDivisible_CompoundPoisson_F001
-- name    : StochLean_Probability_InfinitelyDivisible_CompoundPoisson_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:15:36.081275+00:00
-- url     : https://prove2.me/theorems/0e5f738a-acfb-455a-8dba-705e11240f3e
-- title:
--   StochLean: Probability.InfinitelyDivisible.CompoundPoisson F001

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

section CharacteristicFunction

end CharacteristicFunction

/-- The compound Poisson law parameterized by its finite jump-intensity measure.

The zero measure is handled before normalization, so this definition never uses division by a
zero total mass as mathematics. -/
noncomputable def ofFiniteMeasure (ν : FiniteMeasure G) : ProbabilityMeasure G := by
  classical
  exact if hν : ν = 0 then ProbabilityMeasure.pointMass 0 else law ν.mass ν.normalize
end CompoundPoisson

end ProbabilityTheory


