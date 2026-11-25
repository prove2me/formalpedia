-- Prove2me | Definitions.Def_SourceProof_f01472918deb39a4a3d4b12e
-- name    : SourceProof_f01472918deb39a4a3d4b12e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:46:00.71074+00:00
-- url     : https://prove2.me/theorems/f8748c88-335d-4a15-9ecb-bb647afcfe36
-- title:
--   StochLean source theorem: MeasureTheory.ProbabilityMeasure.conv_comm

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
theorem _root_.Prove2MeSourceProof.h_f01472918deb39a4a3d4b12e (μ ν : ProbabilityMeasure G) : conv μ ν = conv ν μ := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [_root_.Prove2MeSourceProof.h_fcea44cccdc2e2f35ffe89f9]
  exact Measure.conv_comm (μ : Measure G) (ν : Measure G)
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


