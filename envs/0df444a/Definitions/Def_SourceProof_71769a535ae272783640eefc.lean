-- Prove2me | Definitions.Def_SourceProof_71769a535ae272783640eefc
-- name    : SourceProof_71769a535ae272783640eefc
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:42:26.491468+00:00
-- url     : https://prove2.me/theorems/74bf5c11-b6a7-4f5d-a5ee-19c681d5c160
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.stoppedValue_ae_eq_condExp_of_bounded_le

import Definitions.Def_SourceProof_abd730752414d0d67e6d98a8

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

theorem _root_.Prove2MeSourceProof.h_71769a535ae272783640eefc (hX : Martingale X F P)
    (hprog : IsStronglyProgressive F X) (hr : HasRightContinuousPaths X P)
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    (hστ : σ ≤ τ) {T : ℝ≥0} (hbound : ∀ ω, τ ω ≤ T) :
    stoppedValue X σ =ᵐ[P] P[stoppedValue X τ | hσ.measurableSpace] := by
  have hle := hσ.measurableSpace_mono hτ hστ
  have hs := (_root_.Prove2MeSourceProof.h_abd730752414d0d67e6d98a8 hX) hprog hr hσ
    (fun ω ↦ (hστ ω).trans (hbound ω))
  have ht := (_root_.Prove2MeSourceProof.h_abd730752414d0d67e6d98a8 hX) hprog hr hτ hbound
  exact hs.trans ((condExp_condExp_of_le hle hτ.measurableSpace_le).symm.trans
    (condExp_congr_ae ht).symm)
end MeasureTheory.Martingale


