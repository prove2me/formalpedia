-- Prove2me | Definitions.Def_SourceProof_cce2f2b17a1ce0d26138b150
-- name    : SourceProof_cce2f2b17a1ce0d26138b150
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:58:43.522711+00:00
-- url     : https://prove2.me/theorems/c0e9a968-e3aa-4861-8f5e-1d384662aa33
-- title:
--   StochLean source theorem: MeasureTheory.ProbabilityMeasure.convPow_zero

import Definitions.Def_StochLean_Probability_Convolution_Semigroup_F002

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

@[simp]
theorem _root_.Prove2MeSourceProof.h_cce2f2b17a1ce0d26138b150 (μ : ProbabilityMeasure G) : convPow μ 0 = pointMass (G := G) 0 := rfl
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


