-- Prove2me | Definitions.Def_StochLean_Probability_Convolution_Semigroup_F004
-- name    : StochLean_Probability_Convolution_Semigroup_F004
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:13:21.856581+00:00
-- url     : https://prove2.me/theorems/ca31555f-fc36-43af-8a8d-cf301cd05a40
-- title:
--   StochLean: Probability.Convolution.Semigroup F004

import Definitions.Def_StochLean_Probability_Convolution_Semigroup_F000
import Definitions.Def_StochLean_Probability_Convolution_Semigroup_F003

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

section OrderedReal

end OrderedReal

end MeasureTheory.ProbabilityMeasure

namespace ProbabilityTheory

open MeasureTheory

variable {T G : Type*} [Add T] [AddCommMonoid G] [MeasurableSpace G] [MeasurableAdd₂ G]

/-- The law-level convolution semigroup property, with no identity or continuity bundled in. -/
def IsConvolutionSemigroup (ν : T → ProbabilityMeasure G) : Prop :=
  ∀ s t, ν (s + t) = ProbabilityMeasure.conv (ν s) (ν t)
/-- A nonnegative real convolution semigroup is a basic semigroup all of whose laws are supported
on `[0, ∞)`.  Continuity remains a theorem and is not bundled into this definition. -/
def IsNonnegativeConvolutionSemigroup (ν : ℝ≥0 → ProbabilityMeasure ℝ) : Prop :=
  IsConvolutionSemigroup ν ∧ ∀ t, ProbabilityMeasure.IsNonnegativeLaw (ν t)
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


