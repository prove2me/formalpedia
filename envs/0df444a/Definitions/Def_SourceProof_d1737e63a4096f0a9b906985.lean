-- Prove2me | Definitions.Def_SourceProof_d1737e63a4096f0a9b906985
-- name    : SourceProof_d1737e63a4096f0a9b906985
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:37:13.157304+00:00
-- url     : https://prove2.me/theorems/2d38243f-eac7-4a5c-a328-be01d6df1999
-- title:
--   StochLean source theorem: ProbabilityTheory.IsPoissonProcess.integral_real

import Definitions.Def_SourceProof_bdf8e8b21453a2bac9cdf95f
import Definitions.Def_SourceProof_be3669ac449eeef8b58750e2

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

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {N : ℝ≥0 → Ω → ℕ} {rate : ℝ≥0}

namespace IsPoissonProcess
theorem _root_.Prove2MeSourceProof.h_d1737e63a4096f0a9b906985 (hN : IsPoissonProcess N rate P) (t : ℝ≥0) :
    (∫ ω, (N t ω : ℝ) ∂P) = (rate : ℝ) * t := by
  exact (_root_.Prove2MeSourceProof.h_bdf8e8b21453a2bac9cdf95f ((_root_.Prove2MeSourceProof.h_be3669ac449eeef8b58750e2 hN) t))
end IsPoissonProcess

end ProbabilityTheory


