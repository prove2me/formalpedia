-- Prove2me | Definitions.Def_StochLean_Probability_Process_Stopping_LargeJumpCoverage_F000
-- name    : StochLean_Probability_Process_Stopping_LargeJumpCoverage_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:02:15.757885+00:00
-- url     : https://prove2.me/theorems/d81e3208-6f0e-539a-9882-0c17ff58d4e6
-- title:
--   StochLean: Probability.Process.Stopping.LargeJumpCoverage F000

import Definitions.Def_StochLean_Probability_Process_Stopping_LargeJumpSequence_F000
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Measurable finite-prefix coverage of actual large jumps

The good event is that the first omitted entry in the existing large-jump
sequence is beyond the compact horizon. Local finiteness of cadlag jumps
already proves pointwise escape, and bounded indicator convergence makes the
probability of its complement tend to zero. No jump-count moment is assumed.

On the good event the prefix `range K` covers all positive-time strict large
jumps up to the horizon. Finite indexed lifetimes are distinct, while repeated
infinity remains permitted. These are the actual coverage and uniqueness
inputs required by finite jump removal.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsFiniteMeasure P]

end MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*}

/-- The first omitted actual large-jump lifetime is beyond the horizon. -/
noncomputable def largeJumpCoverageEvent (X : ℝ≥0 → Ω → ℝ) (b : ℝ)
    (T : ℝ≥0) (K : ℕ) : Set Ω :=
  {ω | (T : WithTop ℝ≥0) < largeJumpSequence X b K ω}
end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {b : ℝ}

end MeasureTheory


