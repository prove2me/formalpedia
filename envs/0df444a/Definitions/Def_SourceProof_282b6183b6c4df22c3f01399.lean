-- Prove2me | Definitions.Def_SourceProof_282b6183b6c4df22c3f01399
-- name    : SourceProof_282b6183b6c4df22c3f01399
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:34:05.46092+00:00
-- url     : https://prove2.me/theorems/fb920e9a-091d-4ea9-a673-5717706119fa
-- title:
--   StochLean source theorem: ProbabilityTheory.IsPoissonProcess.integral_real_increment_sq

import Definitions.Def_StochLean_Probability_Process_Poisson_Basic_F000
import Definitions.Def_SourceProof_a820ef04cd6f2fb1746b6d33

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
theorem _root_.Prove2MeSourceProof.h_282b6183b6c4df22c3f01399 (hN : IsPoissonProcess N rate P)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ ω, ((N t ω : ℝ) - (N s ω : ℝ)) ^ 2 ∂P) =
      ((rate : ℝ) * ((t : ℝ) - s)) ^ 2 + (rate : ℝ) * ((t : ℝ) - s) := by
  have he : (fun ω ↦ ((N t ω - N s ω : ℕ) : ℝ) ^ 2) =ᵐ[P]
      fun ω ↦ ((N t ω : ℝ) - (N s ω : ℝ)) ^ 2 := by
    filter_upwards [hN.monotonePaths] with ω hω
    rw [Nat.cast_sub (hω hst)]
  rw [← integral_congr_ae he, (_root_.Prove2MeSourceProof.h_a820ef04cd6f2fb1746b6d33 (hN.incrementLaw s t hst))]
  simp only [NNReal.coe_mul, NNReal.coe_sub hst]
end IsPoissonProcess

end ProbabilityTheory


