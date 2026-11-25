-- Prove2me | Definitions.Def_SourceProof_1f543e8baf9d2824a28693b7
-- name    : SourceProof_1f543e8baf9d2824a28693b7
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:14:52.71236+00:00
-- url     : https://prove2.me/theorems/1826607c-0792-4c2b-89d1-56855c70ef97
-- title:
--   StochLean source theorem: ProbabilityTheory.isStoppingTime_nextOscillationTime

import Batteries.Tactic.OpenPrivate
import Definitions.Def_StochLean_Probability_Process_Stopping_Oscillation_F000
import Definitions.Def_StochLean_Probability_Process_Stopping_Oscillation_F001
import Definitions.Def_SourceProof_3b6770fe33c80a2ec52a585f
import Definitions.Def_SourceProof_b755025803f0c28ce74bcca6
import Definitions.Def_SourceProof_d758c5fe1bf7eec6f7a3ad7f

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

variable {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}

theorem _root_.Prove2MeSourceProof.h_1f543e8baf9d2824a28693b7 (hX : Adapted F X) (hF : F.IsUsual P)
    (hr : HasRightContinuousPaths X P) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
    (ε : ℝ) : IsStoppingTime F (nextOscillationTime X ε τ) := by
  have ha : Adapted F (X - stoppedProcess X τ) := fun t ↦
    (hX t).sub (((_root_.Prove2MeSourceProof.h_d758c5fe1bf7eec6f7a3ad7f hX.stronglyAdapted) hF hr hτ).adapted t)
  have hreg : ProbabilityTheory.HasRightContinuousPaths (X - stoppedProcess X τ) P :=
    hr.mono fun _ hω ↦ rightContinuous_sub_stopped hω
  exact (_root_.Prove2MeSourceProof.h_b755025803f0c28ce74bcca6 ha) hF hreg ε
end ProbabilityTheory


