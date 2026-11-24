-- Prove2me | Definitions.Def_SourceProof_02815602af01541f2a91721d
-- name    : SourceProof_02815602af01541f2a91721d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:47:53.513291+00:00
-- url     : https://prove2.me/theorems/23bc87e9-c7c4-460b-82a3-c7e2ac256ba8
-- title:
--   StochLean source theorem: ProbabilityTheory.IsContinuousConvolutionSemigroup.isConvolutionSemigroup

import Definitions.Def_StochLean_Probability_Convolution_Semigroup_F005

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

namespace IsContinuousConvolutionSemigroup
theorem _root_.Prove2MeSourceProof.h_02815602af01541f2a91721d
    {ν : ℝ≥0 → ProbabilityMeasure G} (hν : IsContinuousConvolutionSemigroup ν) :
    IsConvolutionSemigroup ν :=
  hν.1
end IsContinuousConvolutionSemigroup

section Metrizable

open TopologicalSpace

variable [PseudoMetrizableSpace G] [SecondCountableTopology G] [BorelSpace G]
  [ContinuousAdd G]

end Metrizable

section Real

end Real

end Continuous

end ProbabilityTheory


