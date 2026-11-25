-- Prove2me | Definitions.Def_StochLean_Probability_Martingale_OptionalSampling_ContinuousStopping_F000
-- name    : StochLean_Probability_Martingale_OptionalSampling_ContinuousStopping_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:46:15.393864+00:00
-- url     : https://prove2.me/theorems/ad783477-6166-53eb-a989-e0dac2e38802
-- title:
--   StochLean: Probability.Martingale.OptionalSampling.ContinuousStopping F000

import Definitions.Def_StochLean_Probability_Martingale_OptionalSampling_ContinuousTime_F000
import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F000
import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F001
import Definitions.Def_SourceProof_7ed2f005446d5374aeb1a05e

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Stopping continuous-time martingales

The bounded optional-sampling theorem is transported to Mathlib's canonical
`WithTop`-valued stopping times. Splitting on the ordering of two stopping times
then gives the minimum formula. In particular a stopped martingale is a
martingale for the original filtration, not merely the stopped filtration.

Source: Protter I.17 and the corollary of I.18. The unrestricted UI conclusion
of I.18 additionally needs the unbounded optional-sampling theorem.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P] [SigmaFiniteFiltration P F]

private theorem condExp_stoppedValue_restrict_le (hX : Martingale X F P)
    (hprog : IsStronglyProgressive F X) (hr : HasRightContinuousPaths X P)
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    {T : ℝ≥0} (hbound : ∀ ω, τ ω ≤ T) :
    P[stoppedValue X τ | hσ.measurableSpace] =ᵐ[P.restrict {ω | τ ω ≤ σ ω}]
      stoppedValue X τ := by
  have hint := (_root_.Prove2MeSourceProof.h_7ed2f005446d5374aeb1a05e hX) hprog hr hτ hbound
  have hevent := hτ.measurableSet_le_stopping_time hσ
  rw [ae_eq_restrict_iff_indicator_ae_eq (hτ.measurableSpace_le _ hevent)]
  refine (condExp_indicator hint (hτ.measurableSet_stopping_time_le hσ)).symm.trans ?_
  have hi := hint.indicator (hτ.measurableSpace_le _ hevent)
  have hm : StronglyMeasurable[hσ.measurableSpace]
      ({ω | τ ω ≤ σ ω}.indicator (stoppedValue X τ)) := by
    refine StronglyMeasurable.stronglyMeasurable_of_measurableSpace_le_on hevent ?_
      ((measurable_stoppedValue hprog hτ).stronglyMeasurable.indicator hevent) ?_
    · intro A hA
      rw [Set.inter_comm _ A] at hA ⊢
      rw [hτ.measurableSet_inter_le_iff hσ, IsStoppingTime.measurableSet_min_iff hτ hσ] at hA
      exact hA.2
    · intro ω hω
      exact Set.indicator_of_notMem hω _
  exact condExp_of_aestronglyMeasurable' hσ.measurableSpace_le hm.aestronglyMeasurable hi
end MeasureTheory.Martingale


