-- Prove2me | Definitions.Def_SourceProof_81fed43029cb26012ba5024c
-- name    : SourceProof_81fed43029cb26012ba5024c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:21:59.601084+00:00
-- url     : https://prove2.me/theorems/9f3ce5f3-51df-4381-9649-a3b12c470514
-- title:
--   StochLean source theorem: MeasureTheory.measure_exists_norm_lt_le_firstExit_stopped

import Definitions.Def_SourceProof_30084ca22095a3cc9120cd78

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

theorem _root_.Prove2MeSourceProof.h_81fed43029cb26012ba5024c {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} (hr : ProbabilityTheory.HasRightContinuousPaths X P)
    (a : ℝ) (T : ℝ≥0) :
    P {ω | ∃ t ≤ T, a < ‖X t ω‖} ≤
      P {ω | a ≤ ‖stoppedProcess X (hittingAfter X {x | a < ‖x‖} 0) T ω‖} := by
  apply measure_mono_ae
  filter_upwards [hr] with ω hω
  exact _root_.Prove2MeSourceProof.h_30084ca22095a3cc9120cd78 hω
end MeasureTheory


