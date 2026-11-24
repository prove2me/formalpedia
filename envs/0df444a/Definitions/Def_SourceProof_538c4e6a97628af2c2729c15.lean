-- Prove2me | Definitions.Def_SourceProof_538c4e6a97628af2c2729c15
-- name    : SourceProof_538c4e6a97628af2c2729c15
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:13:24.821435+00:00
-- url     : https://prove2.me/theorems/8eb0ced9-2227-4fc5-ab4c-e8992038f356
-- title:
--   StochLean source theorem: MeasureTheory.ProbabilityMeasure.coe_pointMass

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

omit [AddCommMonoid G] [MeasurableAdd₂ G] in
@[simp, norm_cast]
theorem _root_.Prove2MeSourceProof.h_538c4e6a97628af2c2729c15 (x : G) :
    ((pointMass x : ProbabilityMeasure G) : Measure G) = Measure.dirac x :=
  rfl
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

section Metrizable

open TopologicalSpace

variable [PseudoMetrizableSpace G] [SecondCountableTopology G] [BorelSpace G]
  [ContinuousAdd G]

end Metrizable

section Real

end Real

end Continuous

end ProbabilityTheory


