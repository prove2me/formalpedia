-- Prove2me | Definitions.Def_SourceProof_988ec49bcccd24848c73e05d
-- name    : SourceProof_988ec49bcccd24848c73e05d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:16:17.799649+00:00
-- url     : https://prove2.me/theorems/88483704-b106-5b61-94dd-ff85d01d9f3f
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.tendsto_eLpNorm_upperApprox_value

import Definitions.Def_SourceProof_d41d71391b3fd8c6b560ed81
import Definitions.Def_SourceProof_d5e0692f6e3d9a9902fd804f

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Bounded optional sampling in continuous time

Upper countable-range stopping times are capped at the deterministic bound.
Their values are conditional expectations of one integrable terminal value,
so they are uniformly integrable. Right continuity yields the almost-sure
limit, and Vitali gives L1 convergence. No bounded-path assumption is used.

The core statement assumes progressive measurability and common-event right
continuity. An everywhere-right-continuous adapted martingale has the former
property by the existing ProcessCore theorem. Transport from an AE regular
version under a usual filtration is kept separate.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P] [SigmaFiniteFiltration P F]

theorem _root_.Prove2MeSourceProof.h_988ec49bcccd24848c73e05d (hX : Martingale X F P)
    (τ : FiniteStoppingTime F) {T : ℝ≥0} (hτ : ∀ ω, τ ω ≤ T)
    (hr : HasRightContinuousPaths X P) :
    Tendsto (fun n ↦ eLpNorm
      ((fun ω ↦ X (τ.upperApprox T n ω) ω) - (fun ω ↦ X (τ ω) ω)) 1 P) atTop (𝓝 0) := by
  have hui := (_root_.Prove2MeSourceProof.h_d5e0692f6e3d9a9902fd804f hX) τ T
  have hlim := _root_.Prove2MeSourceProof.h_d41d71391b3fd8c6b560ed81 τ hτ hr
  exact tendsto_Lp_finite_of_tendsto_ae le_rfl (by simp) hui.1
    (hui.memLp_of_ae_tendsto hlim) hui.2.1 hlim
end MeasureTheory.Martingale


