-- Prove2me | Definitions.Def_SourceProof_e1b62d4f1d9cc68d3a2ef546
-- name    : SourceProof_e1b62d4f1d9cc68d3a2ef546
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:14:18.672747+00:00
-- url     : https://prove2.me/theorems/509079df-1776-5583-8d63-c83a63628982
-- title:
--   StochLean source theorem: MeasureTheory.ProbabilityMeasure.pointMass_zero_conv

import Definitions.Def_SourceProof_538c4e6a97628af2c2729c15
import Definitions.Def_SourceProof_fcea44cccdc2e2f35ffe89f9

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

@[simp]
theorem _root_.Prove2MeSourceProof.h_e1b62d4f1d9cc68d3a2ef546 (μ : ProbabilityMeasure G) : conv (pointMass 0) μ = μ := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [_root_.Prove2MeSourceProof.h_fcea44cccdc2e2f35ffe89f9, _root_.Prove2MeSourceProof.h_538c4e6a97628af2c2729c15]
  exact Measure.dirac_zero_conv _
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


