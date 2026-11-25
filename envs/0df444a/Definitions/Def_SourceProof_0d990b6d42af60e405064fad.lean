-- Prove2me | Definitions.Def_SourceProof_0d990b6d42af60e405064fad
-- name    : SourceProof_0d990b6d42af60e405064fad
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T07:58:56.627232+00:00
-- url     : https://prove2.me/theorems/fd22790c-008c-4c2b-8960-18d27a00ebea
-- title:
--   StochLean source theorem: ProbabilityTheory.ofReal_le_denseRunningSupremum_of_rightContinuous

import Definitions.Def_SourceProof_afd224c326ca9c828da30ca4

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Countable running suprema and pathwise bridges

Generic process-level objects, also used by Brownian path functionals and UCP.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}


theorem _root_.Prove2MeSourceProof.h_0d990b6d42af60e405064fad {X : ℝ≥0 → Ω → ℝ}
    {T t : ℝ≥0} (ht : t ≤ T) {ω : Ω}
    (hX : IsRightContinuousPath (X · ω)) :
    ENNReal.ofReal (X t ω) ≤ denseRunningSupremum X T ω := by
  apply _root_.Prove2MeSourceProof.h_afd224c326ca9c828da30ca4
    (f := fun t ↦ ENNReal.ofReal (X t ω))
    (fun t ↦ ENNReal.continuous_ofReal.continuousAt.comp_continuousWithinAt (hX t)) ht
  intro n
  exact le_iSup (fun n ↦ ENNReal.ofReal (X (ProbabilityTheory.denseTimeUpTo T n) ω)) n
end ProbabilityTheory


