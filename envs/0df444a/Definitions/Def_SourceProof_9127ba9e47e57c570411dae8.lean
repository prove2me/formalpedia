-- Prove2me | Definitions.Def_SourceProof_9127ba9e47e57c570411dae8
-- name    : SourceProof_9127ba9e47e57c570411dae8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:15:31.597158+00:00
-- url     : https://prove2.me/theorems/e537611e-fa57-428b-bd26-f4794038a9cb
-- title:
--   StochLean source theorem: ProbabilityTheory.HasRightContinuousPaths.stoppedProcess

import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F000
import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
import Definitions.Def_SourceProof_38b6716030de814054336ad8
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

namespace HasRightContinuousPaths
theorem _root_.Prove2MeSourceProof.h_9127ba9e47e57c570411dae8 (hX : HasRightContinuousPaths X P)
    (τ : Ω → WithTop ℝ≥0) : HasRightContinuousPaths (stoppedProcess X τ) P := by
  filter_upwards [hX] with ω hω
  cases hτ : τ ω with
  | top =>
    simpa only [MeasureTheory.stoppedProcess, hτ, min_eq_left le_top,
      WithTop.untopA, WithTop.untopD_coe] using hω
  | coe T =>
    simpa only [MeasureTheory.stoppedProcess, hτ, ← WithTop.coe_min,
      WithTop.untopA, WithTop.untopD_coe] using (_root_.Prove2MeSourceProof.h_38b6716030de814054336ad8 hω) T
end HasRightContinuousPaths

end ProbabilityTheory


