-- Prove2me | Definitions.Def_StochLean_Probability_Martingale_OptionalSampling_ContinuousTime_F000
-- name    : StochLean_Probability_Martingale_OptionalSampling_ContinuousTime_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T07:59:44.413884+00:00
-- url     : https://prove2.me/theorems/656785ba-836f-4cea-8b88-b81bf7422632
-- title:
--   StochLean: Probability.Martingale.OptionalSampling.ContinuousTime F000

import Definitions.Def_StochLean_Probability_Process_Stopping_Approximation_F000
import Definitions.Def_StochLean_Probability_Process_Stopping_Approximation_F001
import Definitions.Def_SourceProof_40787295ae568a8b7553a55a
import Definitions.Def_SourceProof_9c038e074e5d5bfe1fc302cb
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

omit [IsFiniteMeasure P] in
private theorem upperApprox_value_ae_eq_condExp (hX : Martingale X F P)
    (τ : FiniteStoppingTime F) (T : ℝ≥0) (n : ℕ) :
    (fun ω ↦ X (τ.upperApprox T n ω) ω) =ᵐ[P]
      P[X T | (τ.upperApprox T n).measurableSpace] := by
  let σ := τ.upperApprox T n
  have hcount : (Set.range σ.withTop).Countable := by
    apply (((_root_.Prove2MeSourceProof.h_9c038e074e5d5bfe1fc302cb τ) T n).image
      (fun s : ℝ≥0 ↦ (s : WithTop ℝ≥0))).mono
    rintro t ⟨ω, rfl⟩
    exact ⟨σ ω, ⟨ω, rfl⟩, rfl⟩
  exact hX.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range σ.isStoppingTime
    (fun ω ↦ WithTop.coe_le_coe.mpr ((_root_.Prove2MeSourceProof.h_40787295ae568a8b7553a55a τ) T n ω)) hcount
end MeasureTheory.Martingale


