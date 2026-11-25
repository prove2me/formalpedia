-- Prove2me | Definitions.Def_SourceProof_92518556c38a5050070a00b5
-- name    : SourceProof_92518556c38a5050070a00b5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:25:42.038469+00:00
-- url     : https://prove2.me/theorems/58df1ba8-7920-5a56-baa8-f541339d816b
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.elementaryIntegralProcess_const_mul_integrator

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F001
import Definitions.Def_SourceProof_11d1e52ae792291cfc25906e

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Linearity of the elementary integral process in its integrator -/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {H : ℝ≥0 → Ω → ℝ}

namespace IsSimplePredictable
theorem _root_.Prove2MeSourceProof.h_92518556c38a5050070a00b5
    (hH : IsSimplePredictable H F) (c : ℝ) (X : ℝ≥0 → Ω → ℝ) :
    hH.elementaryIntegralProcess (fun t ω ↦ c * X t ω) = c • hH.elementaryIntegralProcess X := by
  funext t
  exact (_root_.Prove2MeSourceProof.h_11d1e52ae792291cfc25906e hH) c (fun s ω ↦ X (min s t) ω)
end IsSimplePredictable

end ProbabilityTheory


