-- Prove2me | Definitions.Def_SourceProof_d41d71391b3fd8c6b560ed81
-- name    : SourceProof_d41d71391b3fd8c6b560ed81
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:05:44.091504+00:00
-- url     : https://prove2.me/theorems/d7202c1f-b0b5-562b-a64e-f5687470dad7
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.ae_tendsto_upperApprox_value

import Definitions.Def_StochLean_Probability_Process_Stopping_Approximation_F000
import Definitions.Def_StochLean_Probability_Process_Stopping_Approximation_F001
import Definitions.Def_SourceProof_f6e38702caec580acfe72e3b
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Probability.Martingale.OptionalSampling

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

omit [IsFiniteMeasure P] [SigmaFiniteFiltration P F] in
theorem _root_.Prove2MeSourceProof.h_d41d71391b3fd8c6b560ed81 (τ : FiniteStoppingTime F) {T : ℝ≥0}
    (hτ : ∀ ω, τ ω ≤ T) (hr : HasRightContinuousPaths X P) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ X (τ.upperApprox T n ω) ω) atTop (𝓝 (X (τ ω) ω)) := by
  filter_upwards [hr] with ω hω
  exact (hω (τ ω)).tendsto.comp ((_root_.Prove2MeSourceProof.h_f6e38702caec580acfe72e3b τ) hτ ω)
end MeasureTheory.Martingale


