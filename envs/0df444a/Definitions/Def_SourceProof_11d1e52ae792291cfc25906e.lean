-- Prove2me | Definitions.Def_SourceProof_11d1e52ae792291cfc25906e
-- name    : SourceProof_11d1e52ae792291cfc25906e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:26:16.485366+00:00
-- url     : https://prove2.me/theorems/7a076869-0415-469a-8258-1f33e1f4e422
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.elementaryIntegral_const_mul_integrator

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F002
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F003
import Definitions.Def_SourceProof_3ad064b37d71e89ec9f818b4

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Elementary linearity in the integrator

These declarations retain their original public names and statements. They live below
good-integrator stability so that the source simple-process algebra can reuse them directly.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

namespace IsSimplePredictable
theorem _root_.Prove2MeSourceProof.h_11d1e52ae792291cfc25906e
    {H : ℝ≥0 → Ω → ℝ} (hH : IsSimplePredictable H F) (c : ℝ) (X : ℝ≥0 → Ω → ℝ) :
    hH.elementaryIntegral (fun t ω ↦ c * X t ω) = fun ω ↦ c * hH.elementaryIntegral X ω :=
  (_root_.Prove2MeSourceProof.h_3ad064b37d71e89ec9f818b4 hH.choose) c X
end IsSimplePredictable

end ProbabilityTheory


