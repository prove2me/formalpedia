-- Prove2me | Definitions.Def_SourceProof_d27c5b9383fd22e9caafc8fd
-- name    : SourceProof_d27c5b9383fd22e9caafc8fd
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:34:54.375812+00:00
-- url     : https://prove2.me/theorems/10aed476-d7b1-40e6-9610-9d9b819753eb
-- title:
--   StochLean source theorem: ProbabilityTheory.monotone_cappedNormExitSequence

import Definitions.Def_StochLean_Probability_Process_Stopping_CadlagExitLocalization_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Capped open norm exits for cadlag localization

The stopping sequence is the existing open norm hit, capped by its increasing
integer threshold. Cadlag compact bounds imply divergence. Strictly before
the exit, the path is bounded by the threshold, and the same bound holds for
its left limit at the exit. A bound on positive-time jumps controls overshoot.

Without a jump bound the stopped process is not claimed to be bounded. Only
its jumps away from the stopping endpoint are at most twice the threshold;
the non-strict inequality and the exceptional endpoint are retained.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω}

theorem _root_.Prove2MeSourceProof.h_d27c5b9383fd22e9caafc8fd (X : ℝ≥0 → Ω → ℝ) :
    Monotone (cappedNormExitSequence X) := by
  intro n m hnm ω
  apply min_le_min
  · apply hittingAfter_anti X 0 _ ω
    intro x hx
    exact (show ((n + 1 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) from
      Nat.cast_le.mpr (Nat.add_le_add_right hnm 1)).trans_lt hx
  · exact WithTop.coe_le_coe.mpr (Nat.cast_le.mpr (Nat.add_le_add_right hnm 1))
variable {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

end MeasureTheory


