-- Prove2me | Definitions.Def_SourceProof_66fd83be7b48068a9848e468
-- name    : SourceProof_66fd83be7b48068a9848e468
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:27:35.175091+00:00
-- url     : https://prove2.me/theorems/b5853417-a96b-45f5-8224-c6c51cfd9f0e
-- title:
--   StochLean source theorem: ProbabilityTheory.ae_denseRunningSupremum_le_of_ae_le

import Definitions.Def_StochLean_Probability_Process_Path_Supremum_F000
import Definitions.Def_StochLean_Probability_Process_Path_Supremum_F001
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Right-continuous running suprema and real-valued probability bounds

These interfaces use the existing `denseRunningSupremum`, not a second running-supremum
construction. Right continuity recovers strict exceedance at every point of `[0,T]`, including
both endpoints. A finite upper bound is established before converting the extended supremum to
real values. Strict positive-threshold probabilities then give the native `TendstoInMeasure`
conclusion, using a smaller threshold to handle its non-strict norm events.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}


theorem _root_.Prove2MeSourceProof.h_66fd83be7b48068a9848e468 {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    {T : ℝ≥0} {K : ℝ} (hX : ∀ t, t ≤ T → ∀ᵐ ω ∂P, X t ω ≤ K) :
    ∀ᵐ ω ∂P, denseRunningSupremum X T ω ≤ ENNReal.ofReal K := by
  have hgrid : ∀ᵐ ω ∂P, ∀ n : ℕ, X (ProbabilityTheory.denseTimeUpTo T n) ω ≤ K := by
    rw [ae_all_iff]
    exact fun n ↦ hX (ProbabilityTheory.denseTimeUpTo T n) (min_le_left _ _)
  filter_upwards [hgrid] with ω hω
  exact iSup_le fun n ↦ ENNReal.ofReal_le_ofReal (hω n)
end ProbabilityTheory


