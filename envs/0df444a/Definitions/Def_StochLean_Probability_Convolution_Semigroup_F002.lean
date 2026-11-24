-- Prove2me | Definitions.Def_StochLean_Probability_Convolution_Semigroup_F002
-- name    : StochLean_Probability_Convolution_Semigroup_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:13:30.255256+00:00
-- url     : https://prove2.me/theorems/5fb201c1-b237-43be-82ff-7ab85db6b567
-- title:
--   StochLean: Probability.Convolution.Semigroup F002

import Definitions.Def_StochLean_Probability_Convolution_Semigroup_F000
import Definitions.Def_StochLean_Probability_Convolution_Semigroup_F001

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Convolution semigroups of probability laws

The basic predicate contains only the semigroup equation.  In particular it does not silently
assert an identity law at time zero or continuity.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory Topology

namespace MeasureTheory.ProbabilityMeasure

variable {G : Type*} [AddCommMonoid G] [MeasurableSpace G] [MeasurableAdd₂ G]

section Topology

open TopologicalSpace

variable [TopologicalSpace G] [PseudoMetrizableSpace G] [SecondCountableTopology G]
  [BorelSpace G] [ContinuousAdd G]

end Topology

/-- The `n`-fold convolution power, including the canonical zeroth power `δ₀`. -/
noncomputable def convPow (μ : ProbabilityMeasure G) : ℕ → ProbabilityMeasure G
  | 0 => pointMass (G := G) 0
  | n + 1 => conv (convPow μ n) μ
section OrderedReal

end OrderedReal

end MeasureTheory.ProbabilityMeasure

namespace ProbabilityTheory

open MeasureTheory

variable {T G : Type*} [Add T] [AddCommMonoid G] [MeasurableSpace G] [MeasurableAdd₂ G]

section Continuous

variable [TopologicalSpace G] [OpensMeasurableSpace G]

section Metrizable

open TopologicalSpace

variable [PseudoMetrizableSpace G] [SecondCountableTopology G] [BorelSpace G]
  [ContinuousAdd G]

end Metrizable

section Real

end Real

end Continuous

end ProbabilityTheory


