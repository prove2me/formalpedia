-- Prove2me | Definitions.Def_SourceProof_fcea44cccdc2e2f35ffe89f9
-- name    : SourceProof_fcea44cccdc2e2f35ffe89f9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:13:16.599803+00:00
-- url     : https://prove2.me/theorems/bfed20d1-9baf-4174-9bdc-7bdf5e5dc6db
-- title:
--   StochLean source theorem: MeasureTheory.ProbabilityMeasure.coe_conv

import Definitions.Def_StochLean_Probability_Convolution_Semigroup_F000

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

@[simp, norm_cast]
theorem _root_.Prove2MeSourceProof.h_fcea44cccdc2e2f35ffe89f9 (μ ν : ProbabilityMeasure G) :
    ((conv μ ν : ProbabilityMeasure G) : Measure G) = (μ : Measure G) ∗ (ν : Measure G) :=
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


