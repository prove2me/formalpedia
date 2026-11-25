-- Prove2me | Definitions.Def_SourceProof_78d563fba2e0cab899d408b9
-- name    : SourceProof_78d563fba2e0cab899d408b9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:56:11.696184+00:00
-- url     : https://prove2.me/theorems/791ef0f1-80d4-4b37-9a1b-49bf96ab2c0a
-- title:
--   StochLean source theorem: MeasureTheory.ProbabilityMeasure.conv_pointMass_zero

import Definitions.Def_StochLean_Probability_Convolution_Semigroup_F001
import Definitions.Def_SourceProof_e1b62d4f1d9cc68d3a2ef546
import Definitions.Def_SourceProof_f01472918deb39a4a3d4b12e

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
theorem _root_.Prove2MeSourceProof.h_78d563fba2e0cab899d408b9 (μ : ProbabilityMeasure G) : conv μ (pointMass 0) = μ := by
  rw [_root_.Prove2MeSourceProof.h_f01472918deb39a4a3d4b12e, _root_.Prove2MeSourceProof.h_e1b62d4f1d9cc68d3a2ef546]
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


