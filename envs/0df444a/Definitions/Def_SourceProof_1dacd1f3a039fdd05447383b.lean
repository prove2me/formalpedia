-- Prove2me | Definitions.Def_SourceProof_1dacd1f3a039fdd05447383b
-- name    : SourceProof_1dacd1f3a039fdd05447383b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:44:30.338344+00:00
-- url     : https://prove2.me/theorems/1c1756a8-fa4f-558e-b4da-e1e7671f3fbc
-- title:
--   StochLean source theorem: ProbabilityTheory.le_toReal_denseRunningSupremum_of_rightContinuous

import Definitions.Def_StochLean_Probability_Process_Path_Supremum_F000
import Definitions.Def_StochLean_Probability_Process_Path_Supremum_F001
import Definitions.Def_SourceProof_0d990b6d42af60e405064fad
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


theorem _root_.Prove2MeSourceProof.h_1dacd1f3a039fdd05447383b
    {X : ℝ≥0 → Ω → ℝ} {T t : ℝ≥0} {ω : Ω} (ht : t ≤ T)
    (hX : IsRightContinuousPath (X · ω)) (hfin : denseRunningSupremum X T ω ≠ ∞) :
    X t ω ≤ (denseRunningSupremum X T ω).toReal :=
  (ENNReal.ofReal_le_iff_le_toReal hfin).mp
    (_root_.Prove2MeSourceProof.h_0d990b6d42af60e405064fad ht hX)
end ProbabilityTheory


