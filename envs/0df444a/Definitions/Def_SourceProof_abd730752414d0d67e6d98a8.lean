-- Prove2me | Definitions.Def_SourceProof_abd730752414d0d67e6d98a8
-- name    : SourceProof_abd730752414d0d67e6d98a8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:36:54.062351+00:00
-- url     : https://prove2.me/theorems/36bc0a31-d314-45eb-8cb2-b7da13215929
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.stoppedValue_ae_eq_condExp_of_bounded

import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F000
import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F001
import Definitions.Def_SourceProof_6451e0733c598e97f97c76a7
import Definitions.Def_SourceProof_a7667c0217d45e8839602222
import Definitions.Def_SourceProof_c3c7921df94e85b3cc715c88
import Definitions.Def_SourceProof_f6ebd573694002332242bbf7

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

theorem _root_.Prove2MeSourceProof.h_abd730752414d0d67e6d98a8 (hX : Martingale X F P)
    (hprog : IsStronglyProgressive F X) (hr : HasRightContinuousPaths X P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) {T : ℝ≥0}
    (hbound : ∀ ω, τ ω ≤ T) : stoppedValue X τ =ᵐ[P] P[X T | hτ.measurableSpace] := by
  let hne := fun ω ↦ ne_top_of_le_ne_top WithTop.coe_ne_top (hbound ω)
  let ρ := ProbabilityTheory.FiniteStoppingTime.ofNotTop hτ hne
  have hρ : ∀ ω, ρ ω ≤ T := fun ω ↦ WithTop.untopA_le (hbound ω)
  have h := (_root_.Prove2MeSourceProof.h_6451e0733c598e97f97c76a7 hX) hprog hr ρ hρ
  simpa only [← _root_.Prove2MeSourceProof.h_a7667c0217d45e8839602222 X ρ, ρ,
    _root_.Prove2MeSourceProof.h_c3c7921df94e85b3cc715c88, _root_.Prove2MeSourceProof.h_f6ebd573694002332242bbf7] using h
end MeasureTheory.Martingale


