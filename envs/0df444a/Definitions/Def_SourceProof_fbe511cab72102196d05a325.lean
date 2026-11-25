-- Prove2me | Definitions.Def_SourceProof_fbe511cab72102196d05a325
-- name    : SourceProof_fbe511cab72102196d05a325
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:47:45.007107+00:00
-- url     : https://prove2.me/theorems/9346ff99-c0fb-49dd-b90e-91baa06aaf8d
-- title:
--   StochLean source theorem: ProbabilityTheory.HasCadlagPaths.largeJumpSumProcess_stoppedProcess

import Batteries.Tactic.OpenPrivate
import Definitions.Def_StochLean_Probability_Process_Path_LargeJumpStopping_F000

open private tsum_jump_transform_stoppedProcess from Definitions.Def_StochLean_Probability_Process_Path_LargeJumpStopping_F000
/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Stopping and event restriction of the actual large-jump sums

Both cumulative processes commute with stopping on the common cadlag event.
The lifetime need not be a stopping time: this is a path identity. The jump
at a finite stopping endpoint is included, while an infinite lifetime leaves
every finite-time value unchanged. At lifetime zero both cumulative sums
are zero, because their actual index interval excludes the initial atom.

Restriction to a fixed sample event commutes exactly, without measurability
or path regularity assumptions. All four identities hold for an arbitrary
real threshold: each of the two truncation maps sends zero to zero. No
global absolute summability, infinite-time value, or new process selector
is introduced.
-/

@[expose] public section

open MeasureTheory StochLean Set Filter
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω}

variable {mΩ : MeasurableSpace Ω} {P : Measure Ω}

namespace HasCadlagPaths

theorem _root_.Prove2MeSourceProof.h_fbe511cab72102196d05a325 (hc : HasCadlagPaths X P)
    (b : ℝ) (τ : Ω → WithTop ℝ≥0) :
    Indistinguishable (largeJumpSumProcess (MeasureTheory.stoppedProcess X τ) b)
      (MeasureTheory.stoppedProcess (largeJumpSumProcess X b) τ) P := by
  filter_upwards [hc] with ω hω t
  exact tsum_jump_transform_stoppedProcess hω (fun z ↦ if b < ‖z‖ then z else 0)
    (by simp only [ite_self]) τ t
end HasCadlagPaths

end ProbabilityTheory


