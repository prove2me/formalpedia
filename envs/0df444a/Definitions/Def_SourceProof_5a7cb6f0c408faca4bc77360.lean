-- Prove2me | Definitions.Def_SourceProof_5a7cb6f0c408faca4bc77360
-- name    : SourceProof_5a7cb6f0c408faca4bc77360
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:46:47.049908+00:00
-- url     : https://prove2.me/theorems/12d3654b-72a0-4b5d-8d41-97baf37213a2
-- title:
--   StochLean source theorem: ProbabilityTheory.IsPoissonProcess.integrable_real

import Definitions.Def_StochLean_Probability_Process_Poisson_IntervalAxioms_F000
import Definitions.Def_SourceProof_ba0c3283c5dd23de3dd55b0c
import Definitions.Def_SourceProof_be3669ac449eeef8b58750e2
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

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {N : ℝ≥0 → Ω → ℕ} {rate : ℝ≥0}

namespace IsPoissonProcess
theorem _root_.Prove2MeSourceProof.h_5a7cb6f0c408faca4bc77360 (hN : IsPoissonProcess N rate P) (t : ℝ≥0) :
    Integrable (fun ω ↦ (N t ω : ℝ)) P :=
  (_root_.Prove2MeSourceProof.h_ba0c3283c5dd23de3dd55b0c ((_root_.Prove2MeSourceProof.h_be3669ac449eeef8b58750e2 hN) t))
end IsPoissonProcess

end ProbabilityTheory


