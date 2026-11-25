-- Prove2me | Definitions.Def_SourceProof_462cb4c096a46af71d80ffe1
-- name    : SourceProof_462cb4c096a46af71d80ffe1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:10:07.7799+00:00
-- url     : https://prove2.me/theorems/155cbd01-e908-522f-b448-59b500e9287a
-- title:
--   StochLean source theorem: ProbabilityTheory.le_norm_increment_nextOscillationTime

import Batteries.Tactic.OpenPrivate
import Definitions.Def_StochLean_Probability_Process_Stopping_Oscillation_F001
import Definitions.Def_SourceProof_03150f91ce36a45c910d7721
import Definitions.Def_SourceProof_8a10a253783a248343a8d5f3

open private rightContinuous_sub_stopped from Definitions.Def_StochLean_Probability_Process_Stopping_Oscillation_F001
/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Recursive oscillation stopping times

The next time is the existing first hit of `X - X^tau`, so it never evaluates an
unprovided value `X_infinity`. For a positive threshold, finite successive times
are strictly separated and their sampled values differ by at least the threshold.
Cadlag paths therefore force the actual recursive times to tend to infinity.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_462cb4c096a46af71d80ffe1 {ε : ℝ} (hε : 0 ≤ ε)
    (τ : Ω → WithTop ℝ≥0) {ω : Ω} (hX : IsRightContinuousPath (X · ω))
    (hne : nextOscillationTime X ε τ ω ≠ ⊤) :
    ε ≤ ‖X (nextOscillationTime X ε τ ω).untopA ω - X (τ ω).untopA ω‖ := by
  have hR := _root_.Prove2MeSourceProof.h_03150f91ce36a45c910d7721 (rightContinuous_sub_stopped hX) hne
  have htime : τ ω ≤ ((ProbabilityTheory.nextOscillationTime X ε τ ω).untopA : WithTop ℝ≥0) := by
    rw [WithTop.untopA_eq_untop hne, WithTop.coe_untop]
    exact _root_.Prove2MeSourceProof.h_8a10a253783a248343a8d5f3 hε τ ω
  change ε ≤ ‖X (ProbabilityTheory.nextOscillationTime X ε τ ω).untopA ω -
    stoppedProcess X τ (ProbabilityTheory.nextOscillationTime X ε τ ω).untopA ω‖ at hR
  rw [stoppedProcess_eq_of_ge htime] at hR
  exact hR
variable {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}

end ProbabilityTheory


