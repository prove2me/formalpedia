-- Prove2me | Definitions.Def_SourceProof_4f959de634195da08dfdbf83
-- name    : SourceProof_4f959de634195da08dfdbf83
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:16:40.392362+00:00
-- url     : https://prove2.me/theorems/96252da8-f1cb-5a55-b6d3-1f3d754d03d5
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.eLpNorm_finiteStoppingTime_min_le

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_Path_RightContinuous_F000
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F004
import Definitions.Def_SourceProof_29d33b95cf42be6716ddb60d
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

theorem _root_.Prove2MeSourceProof.h_4f959de634195da08dfdbf83 (hX : Martingale X F P)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    (τ : FiniteStoppingTime F) (T : ℝ≥0) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (fun ω ↦ X (min (τ ω) T) ω) p P ≤ eLpNorm (X T) p P := by
  rw [eLpNorm_congr_ae ((_root_.Prove2MeSourceProof.h_29d33b95cf42be6716ddb60d hX) hF hr τ T)]
  exact eLpNorm_condExp_le_eLpNorm _ hp
end MeasureTheory.Martingale


