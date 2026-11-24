-- Prove2me | Definitions.Def_SourceProof_d332d56749c842e62ff71033
-- name    : SourceProof_d332d56749c842e62ff71033
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:57:28.448822+00:00
-- url     : https://prove2.me/theorems/3cc65d19-acac-42b7-a5ac-ca498231cd2f
-- title:
--   StochLean source theorem: MeasureTheory.ProbabilityMeasure.isNonnegativeLaw_pointMass_iff

import Definitions.Def_SourceProof_538c4e6a97628af2c2729c15
import Definitions.Def_SourceProof_fadac03da3eca60469f0808f

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

@[simp]
theorem _root_.Prove2MeSourceProof.h_d332d56749c842e62ff71033 (x : ℝ) :
    IsNonnegativeLaw (pointMass x) ↔ 0 ≤ x := by
  rw [_root_.Prove2MeSourceProof.h_fadac03da3eca60469f0808f]
  simp [_root_.Prove2MeSourceProof.h_538c4e6a97628af2c2729c15]
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


