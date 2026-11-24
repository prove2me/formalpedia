-- Prove2me | Definitions.Def_SourceProof_43a2df67ab5b5e7e533fcfda
-- name    : SourceProof_43a2df67ab5b5e7e533fcfda
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:13:20.028493+00:00
-- url     : https://prove2.me/theorems/1a3a2d02-40d4-44ec-93a2-8e38360c6ae9
-- title:
--   StochLean source theorem: MeasureTheory.ProbabilityMeasure.IsNonnegativeLaw.tendsto

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

namespace IsNonnegativeLaw

theorem _root_.Prove2MeSourceProof.h_43a2df67ab5b5e7e533fcfda {μn : ℕ → ProbabilityMeasure ℝ}
    {μ : ProbabilityMeasure ℝ} (hμn : Tendsto μn atTop (𝓝 μ))
    (hn : ∀ n, IsNonnegativeLaw (μn n)) : IsNonnegativeLaw μ := by
  have hport := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμn
    (F := Set.Ici (0 : ℝ)) isClosed_Ici
  have hseq : (fun n => (μn n : Measure ℝ) (Set.Ici 0)) = (fun _ : ℕ => (1 : ℝ≥0∞)) :=
    funext hn
  rw [hseq, limsup_const] at hport
  apply le_antisymm _ hport
  calc
    (μ : Measure ℝ) (Set.Ici 0) ≤ (μ : Measure ℝ) Set.univ :=
      measure_mono (Set.subset_univ _)
    _ = 1 := by simp
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


