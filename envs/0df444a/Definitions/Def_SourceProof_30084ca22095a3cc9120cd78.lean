-- Prove2me | Definitions.Def_SourceProof_30084ca22095a3cc9120cd78
-- name    : SourceProof_30084ca22095a3cc9120cd78
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:10:27.830883+00:00
-- url     : https://prove2.me/theorems/bd1033d8-74be-5245-9744-1b2ef165a3c7
-- title:
--   StochLean source theorem: MeasureTheory.le_norm_stoppedProcess_hittingAfter_of_exists

import Definitions.Def_SourceProof_03150f91ce36a45c910d7721

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # First-exit reduction of a compact maximum event

A strict exceedance before a finite horizon forces the first-exit stopped value
to have norm at least the threshold. No no-overshoot assertion or measurability
of an uncountable supremum is assumed; the measure statement uses AE inclusion.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_30084ca22095a3cc9120cd78 {a : ℝ} {T : ℝ≥0} {ω : Ω}
    (hr : ProbabilityTheory.IsRightContinuousPath (X · ω))
    (hex : ∃ t ≤ T, a < ‖X t ω‖) :
    a ≤ ‖stoppedProcess X (hittingAfter X {x | a < ‖x‖} 0) T ω‖ := by
  obtain ⟨t, ht, hxt⟩ := hex
  have hhit : hittingAfter X {x | a < ‖x‖} 0 ω ≤ (T : WithTop ℝ≥0) :=
    (hittingAfter_le_of_mem (show (0 : ℝ≥0) ≤ t from bot_le) hxt).trans
      (WithTop.coe_le_coe.mpr ht)
  rw [stoppedProcess_eq_of_ge hhit]
  exact _root_.Prove2MeSourceProof.h_03150f91ce36a45c910d7721 hr
    (ne_top_of_le_ne_top WithTop.coe_ne_top hhit)
end MeasureTheory


