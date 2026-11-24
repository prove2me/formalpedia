-- Prove2me | Definitions.Def_SourceProof_ef369f12801e25b88b9d4546
-- name    : SourceProof_ef369f12801e25b88b9d4546
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T19:17:20.927813+00:00
-- url     : https://prove2.me/theorems/c80b61eb-70af-488c-85c5-3a16b1db2d26
-- title:
--   StochLean source theorem: MeasureTheory.ProbabilityMeasure.convPow_succ

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
theorem _root_.Prove2MeSourceProof.h_ef369f12801e25b88b9d4546 (μ : ProbabilityMeasure G) (n : ℕ) :
    convPow μ (n + 1) = conv (convPow μ n) μ := rfl
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


