-- Prove2me | Definitions.Def_SourceProof_03150f91ce36a45c910d7721
-- name    : SourceProof_03150f91ce36a45c910d7721
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:00:35.75494+00:00
-- url     : https://prove2.me/theorems/85f71e43-ca0c-5188-b91c-fc5b4646c67e
-- title:
--   StochLean source theorem: MeasureTheory.le_norm_hittingAfter_norm_of_ne_top

import Definitions.Def_SourceProof_f275ad31254934483f67a202

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Norm bounds at a right-continuous first exit

Strictly before the first exit the norm is at most the threshold. At a finite
first exit the norm is at least the threshold; jumps may overshoot it. No equality
or upper bound at the stopping endpoint is asserted without additional continuity.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_03150f91ce36a45c910d7721 {a : ℝ} {ω : Ω}
    (hr : ProbabilityTheory.IsRightContinuousPath (X · ω))
    (hne : hittingAfter X {x | a < ‖x‖} 0 ω ≠ ⊤) :
    a ≤ ‖X (hittingAfter X {x | a < ‖x‖} 0 ω).untopA ω‖ := by
  have hmem := _root_.Prove2MeSourceProof.h_f275ad31254934483f67a202 hr hne
  have hsub : {x : ℝ | a < ‖x‖} ⊆ {x | a ≤ ‖x‖} := by
    intro x hx
    exact (show a < ‖x‖ from hx).le
  have hs : closure {x : ℝ | a < ‖x‖} ⊆ {x | a ≤ ‖x‖} :=
    closure_minimal hsub (isClosed_le continuous_const continuous_norm)
  exact hs hmem
variable {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}

end MeasureTheory


