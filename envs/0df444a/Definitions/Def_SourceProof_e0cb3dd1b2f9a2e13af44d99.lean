-- Prove2me | Definitions.Def_SourceProof_e0cb3dd1b2f9a2e13af44d99
-- name    : SourceProof_e0cb3dd1b2f9a2e13af44d99
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:47:02.839087+00:00
-- url     : https://prove2.me/theorems/a5e80530-206d-5100-9e25-45f9f8efe841
-- title:
--   StochLean source theorem: ProbabilityTheory.largeJumpNormSumProcess_indicator

import Batteries.Tactic.OpenPrivate
import Definitions.Def_StochLean_Probability_Process_Path_LargeJumpStopping_F000

open private tsum_jump_transform_indicator from Definitions.Def_StochLean_Probability_Process_Path_LargeJumpStopping_F000
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


theorem _root_.Prove2MeSourceProof.h_e0cb3dd1b2f9a2e13af44d99 (X : ℝ≥0 → Ω → ℝ) (b : ℝ) (S : Set Ω) :
    largeJumpNormSumProcess (fun t ↦ S.indicator (X t)) b =
      fun t ↦ S.indicator (largeJumpNormSumProcess X b t) :=
  tsum_jump_transform_indicator X (fun z ↦ if b < ‖z‖ then ‖z‖ else 0)
    (by simp only [norm_zero, ite_self]) S
variable {mΩ : MeasurableSpace Ω} {P : Measure Ω}

end ProbabilityTheory


