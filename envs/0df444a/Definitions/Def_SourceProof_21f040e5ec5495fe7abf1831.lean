-- Prove2me | Definitions.Def_SourceProof_21f040e5ec5495fe7abf1831
-- name    : SourceProof_21f040e5ec5495fe7abf1831
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:57:36.434375+00:00
-- url     : https://prove2.me/theorems/c5dfec65-adb8-43f0-909f-db86bae5b5b1
-- title:
--   StochLean source theorem: MeasureTheory.ProbabilityMeasure.IsNonnegativeLaw.conv

import Definitions.Def_StochLean_Probability_Convolution_Semigroup_F000
import Definitions.Def_StochLean_Probability_Convolution_Semigroup_F003
import Definitions.Def_SourceProof_fadac03da3eca60469f0808f
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

section Topology

open TopologicalSpace

variable [TopologicalSpace G] [PseudoMetrizableSpace G] [SecondCountableTopology G]
  [BorelSpace G] [ContinuousAdd G]

end Topology

section OrderedReal

namespace IsNonnegativeLaw

theorem _root_.Prove2MeSourceProof.h_21f040e5ec5495fe7abf1831 {μ ν : ProbabilityMeasure ℝ}
    (hμ : IsNonnegativeLaw μ) (hν : IsNonnegativeLaw ν) :
    IsNonnegativeLaw (conv μ ν) := by
  rw [_root_.Prove2MeSourceProof.h_fadac03da3eca60469f0808f] at hμ hν ⊢
  rw [_root_.Prove2MeSourceProof.h_fcea44cccdc2e2f35ffe89f9]
  have hpair : ∀ᵐ z ∂(μ : Measure ℝ).prod (ν : Measure ℝ), 0 ≤ z.1 + z.2 := by
    rw [Measure.ae_prod_iff_ae_ae
      (by measurability : MeasurableSet {z : ℝ × ℝ | 0 ≤ z.1 + z.2})]
    filter_upwards [hμ] with x hx
    filter_upwards [hν] with y hy
    exact add_nonneg hx hy
  exact (ae_map_iff (by fun_prop : AEMeasurable (fun z : ℝ × ℝ => z.1 + z.2)
    ((μ : Measure ℝ).prod (ν : Measure ℝ))) (by measurability)).2 hpair
end IsNonnegativeLaw

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


