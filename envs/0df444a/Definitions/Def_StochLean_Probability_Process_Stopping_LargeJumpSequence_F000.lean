-- Prove2me | Definitions.Def_StochLean_Probability_Process_Stopping_LargeJumpSequence_F000
-- name    : StochLean_Probability_Process_Stopping_LargeJumpSequence_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:46:24.588329+00:00
-- url     : https://prove2.me/theorems/62bc6d8e-ecd2-4e2c-94fe-51b4a0dd0013
-- title:
--   StochLean: Probability.Process.Stopping.LargeJumpSequence F000

import Definitions.Def_StochLean_Probability_Process_Stopping_LargeJumpTimes_F000
import Definitions.Def_StochLean_Probability_Process_Stopping_TotallyInaccessibleJumps_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Enumeration of actual positive-time large jumps

The sequence starts at the first large jump strictly after zero, not at a zero sentinel. Every
finite entry is an actual positive-time jump larger than the threshold; finite entries never
repeat. Once infinity occurs it may repeat. Compact local finiteness forces the sequence to
escape each finite horizon, and the minimality of `nextLargeJump` proves that no large jump is
skipped. Thus an everywhere cadlag adapted process has an actual stopping-time enumeration,
with totally inaccessible entries whenever its positive jumps have that source property.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*}

/-- The actual strict large jumps in increasing order, with infinity after exhaustion.
Index zero is already the first positive-time jump, not an initial-value sentinel. -/
noncomputable def largeJumpSequence (X : ℝ≥0 → Ω → ℝ) (b : ℝ) : ℕ → Ω → WithTop ℝ≥0
  | 0 => nextLargeJump X b (fun _ ↦ 0)
  | n + 1 => nextLargeJump X b (largeJumpSequence X b n)
variable {X : ℝ≥0 → Ω → ℝ} {b : ℝ} {ω : Ω}

end ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {b : ℝ}

end MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} {b : ℝ}

end ProbabilityTheory


