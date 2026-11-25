-- Prove2me | Definitions.Def_SourceProof_bdf8e8b21453a2bac9cdf95f
-- name    : SourceProof_bdf8e8b21453a2bac9cdf95f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:39:33.22386+00:00
-- url     : https://prove2.me/theorems/5f7562fc-b84c-51c2-9b28-3bcbdcbee311
-- title:
--   StochLean source theorem: ProbabilityTheory.HasLaw.integral_natCast_poissonMeasure

import Definitions.Def_StochLean_Probability_Process_Poisson_IntervalAxioms_F000
import Definitions.Def_SourceProof_078c84c962dd10d53b0d34a1
import Mathlib.Analysis.SpecialFunctions.Exponential

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # First moments of the actual Poisson counting process

The Poisson series gives the exact first moment, including rate zero.
The existing law and integrability interfaces transfer it to process values
and real increments. No martingale or bracket condition is assumed.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

namespace HasLaw
theorem _root_.Prove2MeSourceProof.h_bdf8e8b21453a2bac9cdf95f
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {Y : Ω → ℕ} {r : ℝ≥0}
    (hY : HasLaw Y (poissonMeasure r) P) : (∫ ω, (Y ω : ℝ) ∂P) = r := by
  calc
    _ = ∫ n : ℕ, (n : ℝ) ∂poissonMeasure r := hY.integral_comp (by fun_prop)
    _ = r := _root_.Prove2MeSourceProof.h_078c84c962dd10d53b0d34a1 r
end HasLaw

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {N : ℝ≥0 → Ω → ℕ} {rate : ℝ≥0}

end ProbabilityTheory


