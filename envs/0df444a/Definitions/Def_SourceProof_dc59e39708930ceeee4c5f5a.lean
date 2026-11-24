-- Prove2me | Definitions.Def_SourceProof_dc59e39708930ceeee4c5f5a
-- name    : SourceProof_dc59e39708930ceeee4c5f5a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:45:05.647809+00:00
-- url     : https://prove2.me/theorems/f335354a-8921-4fda-9a28-4a1d1e0fa72b
-- title:
--   StochLean source theorem: ProbabilityTheory.IsPoissonProcess.integrable_real_increment_sq

import Definitions.Def_StochLean_Probability_Process_Poisson_Basic_F000
import Definitions.Def_SourceProof_50b31e692ed3eaa804a412d7

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

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {N : ℝ≥0 → Ω → ℕ} {rate : ℝ≥0}

namespace IsPoissonProcess
theorem _root_.Prove2MeSourceProof.h_dc59e39708930ceeee4c5f5a (hN : IsPoissonProcess N rate P)
    {s t : ℝ≥0} (hst : s ≤ t) :
    Integrable (fun ω ↦ ((N t ω : ℝ) - (N s ω : ℝ)) ^ 2) P := by
  refine (_root_.Prove2MeSourceProof.h_50b31e692ed3eaa804a412d7 (hN.incrementLaw s t hst)).congr ?_
  filter_upwards [hN.monotonePaths] with ω hω
  rw [Nat.cast_sub (hω hst)]
end IsPoissonProcess

end ProbabilityTheory


