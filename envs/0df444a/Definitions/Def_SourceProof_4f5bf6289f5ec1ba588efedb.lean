-- Prove2me | Definitions.Def_SourceProof_4f5bf6289f5ec1ba588efedb
-- name    : SourceProof_4f5bf6289f5ec1ba588efedb
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:50:58.227149+00:00
-- url     : https://prove2.me/theorems/e815b4e6-2946-5174-9c55-2a07eac24729
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.stoppedValue_min_ae_eq_condExp_of_bounded

import Definitions.Def_StochLean_Probability_Martingale_OptionalSampling_ContinuousStopping_F000
import Definitions.Def_SourceProof_71769a535ae272783640eefc
import Definitions.Def_SourceProof_7ed2f005446d5374aeb1a05e

open private condExp_stoppedValue_restrict_le from Definitions.Def_StochLean_Probability_Martingale_OptionalSampling_ContinuousStopping_F000
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


theorem _root_.Prove2MeSourceProof.h_4f5bf6289f5ec1ba588efedb (hX : Martingale X F P)
    (hprog : IsStronglyProgressive F X) (hr : HasRightContinuousPaths X P)
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    {T : ℝ≥0} (hbound : ∀ ω, τ ω ≤ T) :
    stoppedValue X (fun ω ↦ min (σ ω) (τ ω)) =ᵐ[P]
      P[stoppedValue X τ | hσ.measurableSpace] := by
  refine ((_root_.Prove2MeSourceProof.h_71769a535ae272783640eefc hX) hprog hr (hσ.min hτ) hτ
    (fun _ ↦ min_le_right _ _) hbound).trans ?_
  refine ae_of_ae_restrict_of_ae_restrict_compl {ω | σ ω ≤ τ ω} ?_ ?_
  · exact condExp_min_stopping_time_ae_eq_restrict_le hσ hτ
  · have heq : P[stoppedValue X τ | (hσ.min hτ).measurableSpace] =ᵐ[
        P.restrict {ω | τ ω ≤ σ ω}] P[stoppedValue X τ | hσ.measurableSpace] := by
      refine (show P[stoppedValue X τ | (hσ.min hτ).measurableSpace] =ᵐ[
        P.restrict {ω | τ ω ≤ σ ω}] P[stoppedValue X τ | hτ.measurableSpace] from ?_).trans ?_
      · rw [hσ.measurableSpace_min hτ, inf_comm, ← hτ.measurableSpace_min hσ]
        exact condExp_min_stopping_time_ae_eq_restrict_le hτ hσ
      · rw [condExp_of_stronglyMeasurable hτ.measurableSpace_le
          (measurable_stoppedValue hprog hτ).stronglyMeasurable
          ((_root_.Prove2MeSourceProof.h_7ed2f005446d5374aeb1a05e hX) hprog hr hτ hbound)]
        exact (condExp_stoppedValue_restrict_le hX hprog hr hσ hτ hbound).symm
    rw [ae_restrict_iff'
      (hσ.measurableSpace_le _ (hσ.measurableSet_le_stopping_time hτ).compl)]
    rw [Filter.EventuallyEq, ae_restrict_iff'
      (hτ.measurableSpace_le _ (hτ.measurableSet_le_stopping_time hσ))] at heq
    filter_upwards [heq] with ω hω hmem
    exact hω (le_of_not_ge hmem)
end MeasureTheory.Martingale


