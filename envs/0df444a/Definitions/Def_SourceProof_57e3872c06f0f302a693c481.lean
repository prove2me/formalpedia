-- Prove2me | Definitions.Def_SourceProof_57e3872c06f0f302a693c481
-- name    : SourceProof_57e3872c06f0f302a693c481
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:07:20.5294+00:00
-- url     : https://prove2.me/theorems/13cb7b86-59b0-44c9-b0cd-373aeeae0154
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.elementaryIntegralProcess_indicator_integrator

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F001
import Definitions.Def_SourceProof_e62e235b33c1e53765d13c17

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Event masks in the source integrator

These exact finite-sum identities include the initial product and require no
measurability, path regularity or semimartingale hypothesis on the integrator.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {H : ℝ≥0 → Ω → ℝ}

namespace IsSimplePredictable
theorem _root_.Prove2MeSourceProof.h_57e3872c06f0f302a693c481
    (hH : IsSimplePredictable H F) (X : ℝ≥0 → Ω → ℝ) (s : Set Ω) :
    hH.elementaryIntegralProcess (fun t ↦ s.indicator (X t)) =
      fun t ↦ s.indicator (hH.elementaryIntegralProcess X t) := by
  funext t
  exact (_root_.Prove2MeSourceProof.h_e62e235b33c1e53765d13c17 hH) (fun u ω ↦ X (min u t) ω) s
end IsSimplePredictable

end ProbabilityTheory


