-- Prove2me | Definitions.Def_SourceProof_96c0d23ed76988d7c3d3ef45
-- name    : SourceProof_96c0d23ed76988d7c3d3ef45
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:07:20.936328+00:00
-- url     : https://prove2.me/theorems/22ac784e-2ff7-4e5b-8b4f-e1edbf83ad14
-- title:
--   StochLean source theorem: ProbabilityTheory.HasContinuousPaths.stoppedProcess

import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F000
import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
import Mathlib.Probability.Process.Stopping

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Stopping preserves common-event path regularity -/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {E : Type*} [TopologicalSpace E] {x : ℝ≥0 → E}

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ℝ≥0 → Ω → E}

namespace HasContinuousPaths
theorem _root_.Prove2MeSourceProof.h_96c0d23ed76988d7c3d3ef45 (hX : HasContinuousPaths X P)
    (τ : Ω → WithTop ℝ≥0) : HasContinuousPaths (stoppedProcess X τ) P := by
  filter_upwards [hX] with ω hω
  cases hτ : τ ω with
  | top =>
    simpa only [MeasureTheory.stoppedProcess, hτ, min_eq_left le_top,
      WithTop.untopA, WithTop.untopD_coe] using hω
  | coe T =>
    simpa only [MeasureTheory.stoppedProcess, hτ, ← WithTop.coe_min,
      WithTop.untopA, WithTop.untopD_coe, Function.comp_def, id_eq, ProbabilityTheory.IsContinuousPath] using
      hω.comp (continuous_id.min (continuous_const (y := T)))
end HasContinuousPaths

end ProbabilityTheory


