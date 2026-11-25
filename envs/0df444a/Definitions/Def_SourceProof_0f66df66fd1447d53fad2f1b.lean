-- Prove2me | Definitions.Def_SourceProof_0f66df66fd1447d53fad2f1b
-- name    : SourceProof_0f66df66fd1447d53fad2f1b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:41:49.10957+00:00
-- url     : https://prove2.me/theorems/ce8d06da-e0d4-41e9-9d4c-c2544bf0f7c6
-- title:
--   StochLean source theorem: ProbabilityTheory.Indistinguishable.largeJumpSumProcesses

import Definitions.Def_StochLean_Probability_Process_Path_LargeJumpSum_F000
import Definitions.Def_SourceProof_264d677d5da3fcd447059c80

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The actual large-jump cumulative processes

These are the signed and norm sums of the original jumps strictly larger
than the threshold, over the actual positive-time interval. They do not
select a decomposition or depend on an enumeration. The deterministic
locally finite sum results give common-event cadlag/FV properties and the
exact jumps. Measurability and locally integrable variation are separate
later conclusions, not part of the definitions.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*}

variable {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : ℝ≥0 → Ω → ℝ} {b : ℝ}

namespace Indistinguishable

theorem _root_.Prove2MeSourceProof.h_0f66df66fd1447d53fad2f1b (he : Indistinguishable X Y P) (b : ℝ) :
    Indistinguishable (largeJumpSumProcess X b) (largeJumpSumProcess Y b) P ∧
      Indistinguishable (largeJumpNormSumProcess X b) (largeJumpNormSumProcess Y b) P := by
  constructor <;> filter_upwards [(_root_.Prove2MeSourceProof.h_264d677d5da3fcd447059c80 he)] with ω hω t
  · simp only [ProbabilityTheory.largeJumpSumProcess, hω]
  · simp only [ProbabilityTheory.largeJumpNormSumProcess, hω]
end Indistinguishable

end ProbabilityTheory


