-- Prove2me | Definitions.Def_StochLean_Probability_Process_Stopping_LargeJumpResidual_F000
-- name    : StochLean_Probability_Process_Stopping_LargeJumpResidual_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:10:07.733371+00:00
-- url     : https://prove2.me/theorems/2133ea89-76b1-5df2-81c3-772956d92d48
-- title:
--   StochLean: Probability.Process.Stopping.LargeJumpResidual F000

import Definitions.Def_StochLean_Probability_Process_Path_CadlagWindowMoments_F000
import Definitions.Def_StochLean_Probability_Process_Path_CadlagWindowMoments_F001
import Definitions.Def_StochLean_Probability_Process_Stopping_LargeJumpCoverage_F000
import Definitions.Def_StochLean_Probability_Process_Stopping_TerminalValue_F000
import Mathlib.Topology.Algebra.Group.Basic

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Actual finite-prefix large-jump residuals

The residual removes exactly the first `K` entries of the actual large-jump sequence.
At infinite entries the coefficient is explicitly zero. On the measurable coverage
event all its positive-time jumps on the horizon are small. Fixed-cap short-window
moments are derived from this event, whose complement tends to zero in probability.
No integrability of a random total jump count is required.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*}

/-- Remove a deterministic finite prefix of the actual large-jump enumeration. -/
noncomputable def largeJumpResidual (X : ℝ≥0 → Ω → ℝ) (b : ℝ) (K : ℕ) :
    ℝ≥0 → Ω → ℝ := fun t ω ↦ X t ω -
  ∑ i ∈ Finset.range K, {v | largeJumpSequence X b i v ≤ (t : WithTop ℝ≥0)}.indicator
    (stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ))
      (largeJumpSequence X b i)) ω
variable {X : ℝ≥0 → Ω → ℝ} {ω : Ω} {b : ℝ}

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {b : ℝ}

end MeasureTheory


