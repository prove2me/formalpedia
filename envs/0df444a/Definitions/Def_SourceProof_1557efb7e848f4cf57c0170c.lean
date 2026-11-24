-- Prove2me | Definitions.Def_SourceProof_1557efb7e848f4cf57c0170c
-- name    : SourceProof_1557efb7e848f4cf57c0170c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:59:10.035921+00:00
-- url     : https://prove2.me/theorems/10d2e2ad-d8c9-4436-9860-29b6f2623a1a
-- title:
--   StochLean source theorem: ProbabilityTheory.HasCadlagPaths.stoppedProcess

import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F000
import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
import Definitions.Def_SourceProof_056f0ffa0965e1b3a522e2ff
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

namespace HasCadlagPaths
theorem _root_.Prove2MeSourceProof.h_1557efb7e848f4cf57c0170c (hX : HasCadlagPaths X P)
    (τ : Ω → WithTop ℝ≥0) : HasCadlagPaths (stoppedProcess X τ) P := by
  filter_upwards [hX] with ω hω
  cases hτ : τ ω with
  | top =>
    simpa only [MeasureTheory.stoppedProcess, hτ, min_eq_left le_top,
      WithTop.untopA, WithTop.untopD_coe] using hω
  | coe T =>
    simpa only [MeasureTheory.stoppedProcess, hτ, ← WithTop.coe_min,
      WithTop.untopA, WithTop.untopD_coe] using (_root_.Prove2MeSourceProof.h_056f0ffa0965e1b3a522e2ff hω) T
end HasCadlagPaths

end ProbabilityTheory


