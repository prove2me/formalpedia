-- Prove2me | Definitions.Def_SourceProof_bc31d4fc386dd41a31123691
-- name    : SourceProof_bc31d4fc386dd41a31123691
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:57:04.587545+00:00
-- url     : https://prove2.me/theorems/97f6b5c0-8a24-5cc2-a1ac-b03721bb820f
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.stoppedProcess_of_progressive

import Definitions.Def_StochLean_Probability_Martingale_OptionalSampling_ContinuousTime_F000
import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F000
import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F001
import Definitions.Def_SourceProof_4f5bf6289f5ec1ba588efedb

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


theorem _root_.Prove2MeSourceProof.h_bc31d4fc386dd41a31123691 (hX : Martingale X F P)
    (hprog : IsStronglyProgressive F X) (hr : HasRightContinuousPaths X P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    Martingale (stoppedProcess X τ) F P := by
  refine ⟨hprog.stronglyAdapted_stoppedProcess hτ, ?_⟩
  intro s t hst
  have h := (_root_.Prove2MeSourceProof.h_4f5bf6289f5ec1ba588efedb hX) hprog hr
    (isStoppingTime_const F s) ((isStoppingTime_const F t).min hτ)
    (fun _ ↦ min_le_left _ _)
  rw [IsStoppingTime.measurableSpace_const] at h
  simpa only [stoppedProcess_eq_stoppedValue, ← min_assoc,
    min_eq_left (WithTop.coe_le_coe.mpr hst)] using h.symm
end MeasureTheory.Martingale


