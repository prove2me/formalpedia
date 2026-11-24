-- Prove2me | Definitions.Def_SourceProof_fadac03da3eca60469f0808f
-- name    : SourceProof_fadac03da3eca60469f0808f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:13:24.55825+00:00
-- url     : https://prove2.me/theorems/dc109d9a-7cec-4096-a7d9-7ce497ec89dd
-- title:
--   StochLean source theorem: MeasureTheory.ProbabilityMeasure.isNonnegativeLaw_iff_ae

import Definitions.Def_StochLean_Probability_Convolution_Semigroup_F003

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

theorem _root_.Prove2MeSourceProof.h_fadac03da3eca60469f0808f (μ : ProbabilityMeasure ℝ) :
    IsNonnegativeLaw μ ↔ ∀ᵐ x ∂(μ : Measure ℝ), 0 ≤ x := by
  constructor
  · intro h
    apply (ae_mem_iff_measure_eq measurableSet_Ici.nullMeasurableSet).2
    simpa [MeasureTheory.ProbabilityMeasure.IsNonnegativeLaw] using h
  · intro h
    have hmass := (ae_mem_iff_measure_eq measurableSet_Ici.nullMeasurableSet).1 h
    simpa [MeasureTheory.ProbabilityMeasure.IsNonnegativeLaw] using hmass
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


