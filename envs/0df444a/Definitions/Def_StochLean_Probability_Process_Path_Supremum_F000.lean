-- Prove2me | Definitions.Def_StochLean_Probability_Process_Path_Supremum_F000
-- name    : StochLean_Probability_Process_Path_Supremum_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:46:15.711139+00:00
-- url     : https://prove2.me/theorems/182b883a-8135-44eb-881c-660f15ab85b8
-- title:
--   StochLean: Probability.Process.Path.Supremum F000

import Definitions.Def_StochLean_Probability_Process_Path_RightContinuous_F000
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Countable running suprema and pathwise bridges

Generic process-level objects, also used by Brownian path functionals and UCP.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- A fixed countable dense grid, retracted to the deterministic interval `[0,T]`.  Retraction by
`min T` retains density in that interval and includes the terminal endpoint whenever a dense-grid
point lies above it. -/
noncomputable def denseTimeUpTo (T : ℝ≥0) (n : ℕ) : ℝ≥0 :=
  min T (TopologicalSpace.denseSeq ℝ≥0 n)
/-- The positive-part running supremum along the canonical dense grid. -/
noncomputable def denseRunningSupremum (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal (X (denseTimeUpTo T n) ω)
end ProbabilityTheory


