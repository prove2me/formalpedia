-- Prove2me | Definitions.Def_SourceProof_23795881371d33084b2010fb
-- name    : SourceProof_23795881371d33084b2010fb
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:26:34.635813+00:00
-- url     : https://prove2.me/theorems/4f9c9b28-2788-42e2-a9f3-fa29ac3a3edd
-- title:
--   StochLean source theorem: ProbabilityTheory.compactDeviation_eq_dense_of_leftContinuous

import Definitions.Def_StochLean_Probability_Process_Path_Caglad_F000
import Definitions.Def_StochLean_Probability_Process_UCP_F001
import Definitions.Def_SourceProof_1217de95d74e06768f3e53ec
import Definitions.Def_SourceProof_845eb3d5bff7aa74f6afa784

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Compact deviations for left-continuous paths

The initial value is included separately from the dense grid. Left continuity
on a half-line imposes no relation between that value and its right limit.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X Y : ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_23795881371d33084b2010fb {T : ℝ≥0} {ω : Ω}
    (hX : IsLeftContinuousPath (X · ω)) (hY : IsLeftContinuousPath (Y · ω)) :
    compactDeviation X Y T ω = max (ENNReal.ofReal ‖X 0 ω - Y 0 ω‖)
      (denseRunningSupremum (fun t ω ↦ ‖X t ω - Y t ω‖) T ω) := by
  apply le_antisymm
  · apply iSup_le
    intro t
    apply iSup_le
    intro ht
    apply _root_.Prove2MeSourceProof.h_1217de95d74e06768f3e53ec
      (fun s ↦ ENNReal.continuous_ofReal.continuousAt.comp_continuousWithinAt
        (((hX s).sub (hY s)).norm)) ht (le_max_left _ _)
    intro n
    exact (le_iSup (fun n ↦ ENNReal.ofReal
      ‖X (ProbabilityTheory.denseTimeUpTo T n) ω - Y (ProbabilityTheory.denseTimeUpTo T n) ω‖) n).trans (le_max_right _ _)
  · apply max_le
    · exact _root_.Prove2MeSourceProof.h_845eb3d5bff7aa74f6afa784 bot_le ω
    · apply iSup_le
      intro n
      exact _root_.Prove2MeSourceProof.h_845eb3d5bff7aa74f6afa784 (min_le_left _ _) ω
end ProbabilityTheory


