-- Prove2me | Definitions.Def_SourceProof_29d33b95cf42be6716ddb60d
-- name    : SourceProof_29d33b95cf42be6716ddb60d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:11:06.344859+00:00
-- url     : https://prove2.me/theorems/6b548cd2-ed34-542a-badd-5189898092cd
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.finiteStoppingTime_min_ae_eq_condExp_terminal

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_Path_RightContinuous_F000
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F004
import Definitions.Def_SourceProof_0ac0eb33cab8f0d0a670e4a9
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.LocalProperty

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Terminal Lp control on finite, unbounded stopping partitions

Stopping the integrator at `T` gives a conditional expectation of `X_T` in the sigma-field
at the original endpoint. The endpoint need not have a deterministic bound.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P] [SigmaFiniteFiltration P F]

theorem _root_.Prove2MeSourceProof.h_29d33b95cf42be6716ddb60d (hX : Martingale X F P)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    (τ : FiniteStoppingTime F) (T : ℝ≥0) :
    (fun ω ↦ X (min (τ ω) T) ω) =ᵐ[P] P[X T | τ.measurableSpace] := by
  have h := (_root_.Prove2MeSourceProof.h_0ac0eb33cab8f0d0a670e4a9 hX) hF hr τ.isStoppingTime
    (isStoppingTime_const F T) (fun _ ↦ le_rfl)
  have heq : MeasureTheory.stoppedValue X (fun ω ↦ min (τ.withTop ω) (T : WithTop ℝ≥0)) =
      fun ω ↦ X (min (τ ω) T) ω := by
    funext ω
    change X (WithTop.untopA (min (τ ω : WithTop ℝ≥0) (T : WithTop ℝ≥0))) ω = _
    rw [← WithTop.coe_min]
    rfl
  change MeasureTheory.stoppedValue X (fun ω ↦ min (τ.withTop ω) (T : WithTop ℝ≥0)) =ᵐ[P]
    P[X T | τ.measurableSpace] at h
  rw [heq] at h
  exact h
end MeasureTheory.Martingale


