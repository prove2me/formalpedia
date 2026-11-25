-- Prove2me | Definitions.Def_SourceProof_a820ef04cd6f2fb1746b6d33
-- name    : SourceProof_a820ef04cd6f2fb1746b6d33
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:45:00.310584+00:00
-- url     : https://prove2.me/theorems/fc7d7a8a-3bff-5568-baed-d0d84b163410
-- title:
--   StochLean source theorem: ProbabilityTheory.HasLaw.integral_natCast_sq_poissonMeasure

import Definitions.Def_SourceProof_bca5f30d001e49e5350a130a
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Topology.Bases
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.LeftRight

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Second moments of Poisson counts

The series shift proves square integrability and the exact second moment.
Ordered real increments inherit both results from their existing Poisson law.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

namespace HasLaw
theorem _root_.Prove2MeSourceProof.h_a820ef04cd6f2fb1746b6d33
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {Y : Ω → ℕ} {r : ℝ≥0}
    (hY : HasLaw Y (poissonMeasure r) P) :
    (∫ ω, (Y ω : ℝ) ^ 2 ∂P) = (r : ℝ) ^ 2 + r := by
  calc
    _ = ∫ n : ℕ, (n : ℝ) ^ 2 ∂poissonMeasure r := hY.integral_comp (by fun_prop)
    _ = (r : ℝ) ^ 2 + r := _root_.Prove2MeSourceProof.h_bca5f30d001e49e5350a130a r
end HasLaw

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {N : ℝ≥0 → Ω → ℕ} {rate : ℝ≥0}

end ProbabilityTheory


