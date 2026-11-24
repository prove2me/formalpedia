-- Prove2me | Definitions.Def_StochLean_Probability_Process_UCP_F001
-- name    : StochLean_Probability_Process_UCP_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:07:01.674046+00:00
-- url     : https://prove2.me/theorems/77572079-62f9-4731-8658-5a2d93b9233c
-- title:
--   StochLean: Probability.Process.UCP F001

import Definitions.Def_StochLean_Probability_Process_UCP_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Uniform convergence on compact time intervals in probability

The compact deviation has an extended nonnegative value, so it never uses a
default real supremum of an unbounded set. Its equality with a countable dense
supremum is proved on right-continuous paths. Measurability is then a theorem,
not an assumption hidden in the definition of an uncountable supremum.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X Y : ℝ≥0 → Ω → ℝ}

/-- Compact-by-compact convergence in probability of the uniform deviations. -/
def TendstoUCP {ι : Type*} (P : Measure Ω) (X : ι → ℝ≥0 → Ω → ℝ)
    (l : Filter ι) (Y : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ T : ℝ≥0, ∀ ε : ℝ≥0∞, 0 < ε →
    Tendsto (fun i ↦ P {ω | ε ≤ compactDeviation (X i) Y T ω}) l (𝓝 0)
end ProbabilityTheory


