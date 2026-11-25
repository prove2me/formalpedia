-- Prove2me | Definitions.Def_SourceProof_dc984e4bcf546833c944556d
-- name    : SourceProof_dc984e4bcf546833c944556d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:47:11.122348+00:00
-- url     : https://prove2.me/theorems/f735e45b-1e39-4820-9c5a-70a292ed2e3c
-- title:
--   StochLean source theorem: ProbabilityTheory.HasCadlagPaths.largeJumpNormSumProcess_stoppedProcess

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

theorem _root_.Prove2MeSourceProof.h_dc984e4bcf546833c944556d (hc : HasCadlagPaths X P)
    (b : ℝ) (τ : Ω → WithTop ℝ≥0) :
    Indistinguishable (largeJumpNormSumProcess (MeasureTheory.stoppedProcess X τ) b)
      (MeasureTheory.stoppedProcess (largeJumpNormSumProcess X b) τ) P := by
  filter_upwards [hc] with ω hω t
  exact tsum_jump_transform_stoppedProcess hω (fun z ↦ if b < ‖z‖ then ‖z‖ else 0)
    (by simp only [norm_zero, ite_self]) τ t
end HasCadlagPaths

end ProbabilityTheory


