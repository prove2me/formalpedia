-- Prove2me | Definitions.Def_StochLean_Probability_Convolution_Semigroup_F005
-- name    : StochLean_Probability_Convolution_Semigroup_F005
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:57:34.273641+00:00
-- url     : https://prove2.me/theorems/5a0bcc27-5c1a-4ed0-b9c4-74c4784a72c9
-- title:
--   StochLean: Probability.Convolution.Semigroup F005

import Definitions.Def_StochLean_Probability_Convolution_Semigroup_F001
import Definitions.Def_StochLean_Probability_Convolution_Semigroup_F004

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

section Continuous

variable [TopologicalSpace G] [OpensMeasurableSpace G]

/-- Continuous refinement on nonnegative real time.  The limit is explicitly from positive times. -/
def IsContinuousConvolutionSemigroup (ν : ℝ≥0 → ProbabilityMeasure G) : Prop :=
  IsConvolutionSemigroup ν ∧
    Tendsto ν (nhdsWithin (0 : ℝ≥0) (Set.Ioi (0 : ℝ≥0)))
      (𝓝 (ProbabilityMeasure.pointMass (G := G) (0 : G)))
section Metrizable

open TopologicalSpace

variable [PseudoMetrizableSpace G] [SecondCountableTopology G] [BorelSpace G]
  [ContinuousAdd G]

end Metrizable

section Real

end Real

end Continuous

end ProbabilityTheory


