-- Prove2me | Definitions.Def_StochLean_Probability_Process_Path_LargeJumpSum_F000
-- name    : StochLean_Probability_Process_Path_LargeJumpSum_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:36:43.436801+00:00
-- url     : https://prove2.me/theorems/c4fc84da-9076-4018-8b4b-ab0a55fdcf72
-- title:
--   StochLean: Probability.Process.Path.LargeJumpSum F000

import Definitions.Def_StochLean_Analysis_PathVariation_LargeJumpSum_F000
import Definitions.Def_StochLean_Probability_Process_Path_FiniteVariation_F000

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

/-- The actual signed sum of positive-time jumps strictly larger than b.
It has no time-zero atom, regardless of the original initial random value. -/
noncomputable def largeJumpSumProcess (X : ℝ≥0 → Ω → ℝ) (b : ℝ) :
    ℝ≥0 → Ω → ℝ := fun t ω ↦ ∑' s : Ioc 0 t,
  if b < ‖jumpProcess X s ω‖ then jumpProcess X s ω else 0
/-- The actual norm sum of positive-time jumps strictly larger than b.
This is not a second total-variation owner; it bounds the signed sum's
existing actual variation on every compact interval. -/
noncomputable def largeJumpNormSumProcess (X : ℝ≥0 → Ω → ℝ) (b : ℝ) :
    ℝ≥0 → Ω → ℝ := fun t ω ↦ ∑' s : Ioc 0 t,
  if b < ‖jumpProcess X s ω‖ then ‖jumpProcess X s ω‖ else 0
variable {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : ℝ≥0 → Ω → ℝ} {b : ℝ}

end ProbabilityTheory


