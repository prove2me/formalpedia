-- Prove2me | Definitions.Def_SourceProof_8a10a253783a248343a8d5f3
-- name    : SourceProof_8a10a253783a248343a8d5f3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:13:35.89173+00:00
-- url     : https://prove2.me/theorems/2144ebbe-ff4e-40e9-b648-cbb4a401d583
-- title:
--   StochLean source theorem: ProbabilityTheory.le_nextOscillationTime

import Definitions.Def_StochLean_Probability_Process_Stopping_Oscillation_F000

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

theorem _root_.Prove2MeSourceProof.h_8a10a253783a248343a8d5f3 {ε : ℝ} (hε : 0 ≤ ε) (τ : Ω → WithTop ℝ≥0) (ω : Ω) :
    τ ω ≤ nextOscillationTime X ε τ ω := by
  cases hτ : τ ω with
  | top =>
    have heq : ProbabilityTheory.nextOscillationTime X ε τ ω = ⊤ := by
      apply hittingAfter_eq_top_iff.mpr
      intro t _
      change ¬ ε < ‖X t ω - stoppedProcess X τ t ω‖
      rw [stoppedProcess_eq_of_le (by rw [hτ]; exact le_top), sub_self, norm_zero]
      exact not_lt_of_ge hε
    rw [heq]
  | coe T =>
    by_contra hn
    have hlt : ProbabilityTheory.nextOscillationTime X ε τ ω < (T : WithTop ℝ≥0) := lt_of_not_ge hn
    obtain ⟨t, ht, hhit⟩ := hittingAfter_lt_iff.mp hlt
    have hstop : stoppedProcess X τ t ω = X t ω := stoppedProcess_eq_of_le
      (by rw [hτ]; exact WithTop.coe_le_coe.mpr ht.2.le)
    change ε < ‖X t ω - stoppedProcess X τ t ω‖ at hhit
    rw [hstop, sub_self, norm_zero] at hhit
    exact not_lt_of_ge hε hhit
variable {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}

end ProbabilityTheory


