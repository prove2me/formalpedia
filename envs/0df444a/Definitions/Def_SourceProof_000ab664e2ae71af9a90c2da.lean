-- Prove2me | Definitions.Def_SourceProof_000ab664e2ae71af9a90c2da
-- name    : SourceProof_000ab664e2ae71af9a90c2da
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:47:50.320724+00:00
-- url     : https://prove2.me/theorems/bc018a5c-bbe7-40fa-9dd0-aaab5b3d824f
-- title:
--   StochLean source theorem: ProbabilityTheory.hasFiniteVariationPaths_iff_ae_forall_horizon

import Definitions.Def_StochLean_Probability_Process_Path_FiniteVariation_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Finite variation on one common path event

The deterministic owners remain Mathlib's bounded and locally bounded variation.
Local finite variation and finite total variation on the half-line are distinct.
Cadlag paths and adaptedness are separate hypotheses, not implicit fields.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

variable {X Y : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem _root_.Prove2MeSourceProof.h_000ab664e2ae71af9a90c2da :
    HasFiniteVariationPaths X P ↔ ∀ᵐ ω ∂P, ∀ T, BoundedVariationOn (fun t ↦ X t ω) (Icc 0 T) := by
  constructor
  · intro h
    filter_upwards [h] with ω hω T
    simpa only [univ_inter] using hω 0 T (mem_univ _) (mem_univ _)
  · intro h
    filter_upwards [h] with ω hω a b _ _
    exact (hω b).mono (fun _ hx ↦ ⟨bot_le, hx.2.2⟩)
end ProbabilityTheory


