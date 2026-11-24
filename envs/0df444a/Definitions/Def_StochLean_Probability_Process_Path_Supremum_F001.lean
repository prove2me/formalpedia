-- Prove2me | Definitions.Def_StochLean_Probability_Process_Path_Supremum_F001
-- name    : StochLean_Probability_Process_Path_Supremum_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:46:21.014803+00:00
-- url     : https://prove2.me/theorems/d1527806-b765-47f7-9795-39d584f4ad56
-- title:
--   StochLean: Probability.Process.Path.Supremum F001

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

/-- Rational times in the compact interval `[0,T]`. -/
abbrev RationalTimeUpTo (T : ℝ≥0) :=
  {q : ℚ // 0 ≤ q ∧ (q : ℝ) ≤ T}
/-- A bounded nonnegative rational time as an `NNReal`. -/
def RationalTimeUpTo.toNNReal {T : ℝ≥0} (q : RationalTimeUpTo T) : ℝ≥0 :=
  ⟨(q : ℝ), by exact_mod_cast q.property.1⟩
/-- The positive-part running supremum over rational times up to `T`.  `ENNReal` is used so that
the countable supremum is total; for a continuous real path on a compact interval it is finite. -/
noncomputable def rationalRunningSupremum (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  ⨆ q : RationalTimeUpTo T, ENNReal.ofReal (X q.toNNReal ω)
end ProbabilityTheory


