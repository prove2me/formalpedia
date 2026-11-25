-- Prove2me | Definitions.Def_SourceProof_8721f78b0017a7455a9a15ba
-- name    : SourceProof_8721f78b0017a7455a9a15ba
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:41:33.896641+00:00
-- url     : https://prove2.me/theorems/7872e40d-216f-413f-9eb6-977463902692
-- title:
--   StochLean source theorem: ProbabilityTheory.largeJumpSumProcesses_initial

import Definitions.Def_StochLean_Probability_Process_Path_LargeJumpSum_F000
import Definitions.Def_SourceProof_d6328de13fa85f3e415f02f0

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

theorem _root_.Prove2MeSourceProof.h_8721f78b0017a7455a9a15ba (X : ℝ≥0 → Ω → ℝ) (b : ℝ) :
    largeJumpSumProcess X b 0 = 0 ∧ largeJumpNormSumProcess X b 0 = 0 :=
  ⟨funext fun ω ↦ (_root_.Prove2MeSourceProof.h_d6328de13fa85f3e415f02f0 X b ω).1,
    funext fun ω ↦ (_root_.Prove2MeSourceProof.h_d6328de13fa85f3e415f02f0 X b ω).2⟩
variable {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : ℝ≥0 → Ω → ℝ} {b : ℝ}

end ProbabilityTheory


