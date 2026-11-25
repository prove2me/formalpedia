-- Prove2me | Definitions.Def_SourceProof_f9163e64a89a6717e7883932
-- name    : SourceProof_f9163e64a89a6717e7883932
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:58:20.005207+00:00
-- url     : https://prove2.me/theorems/fe739cff-06bb-4331-ba3b-8352cf1a1418
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.elementaryIntegralProcess_neg_integrator

import Definitions.Def_SourceProof_92518556c38a5050070a00b5

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
theorem _root_.Prove2MeSourceProof.h_f9163e64a89a6717e7883932
    (hH : IsSimplePredictable H F) (X : ℝ≥0 → Ω → ℝ) :
    hH.elementaryIntegralProcess (-X) = -hH.elementaryIntegralProcess X := by
  change hH.elementaryIntegralProcess (fun t ω ↦ -X t ω) = -hH.elementaryIntegralProcess X
  simpa only [neg_one_mul, neg_one_smul] using
    (_root_.Prove2MeSourceProof.h_92518556c38a5050070a00b5 hH) (-1) X
end IsSimplePredictable

end ProbabilityTheory


