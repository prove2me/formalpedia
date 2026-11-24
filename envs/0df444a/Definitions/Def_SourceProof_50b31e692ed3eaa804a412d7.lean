-- Prove2me | Definitions.Def_SourceProof_50b31e692ed3eaa804a412d7
-- name    : SourceProof_50b31e692ed3eaa804a412d7
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:27:24.786412+00:00
-- url     : https://prove2.me/theorems/53e647f8-8852-4442-bace-37d8e400bf4a
-- title:
--   StochLean source theorem: ProbabilityTheory.HasLaw.integrable_natCast_sq_poissonMeasure

import Definitions.Def_SourceProof_b5b4d599cb73f64707c76f41
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
theorem _root_.Prove2MeSourceProof.h_50b31e692ed3eaa804a412d7
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {Y : Ω → ℕ} {r : ℝ≥0}
    (hY : HasLaw Y (poissonMeasure r) P) : Integrable (fun ω ↦ (Y ω : ℝ) ^ 2) P := by
  have hmap : Integrable (fun n : ℕ ↦ (n : ℝ) ^ 2) (P.map Y) := by
    rw [hY.map_eq]
    exact _root_.Prove2MeSourceProof.h_b5b4d599cb73f64707c76f41 r
  exact (integrable_map_measure (by fun_prop) hY.aemeasurable).mp hmap
end HasLaw

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {N : ℝ≥0 → Ω → ℕ} {rate : ℝ≥0}

end ProbabilityTheory


