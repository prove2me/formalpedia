-- Prove2me | Definitions.Def_SourceProof_e62e235b33c1e53765d13c17
-- name    : SourceProof_e62e235b33c1e53765d13c17
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:55:52.011472+00:00
-- url     : https://prove2.me/theorems/6dc382da-c529-5f20-871c-e5c8876f957b
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.elementaryIntegral_indicator_integrator

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F001
import Definitions.Def_SourceProof_ef56ad646743a44ff20b8cc8

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
theorem _root_.Prove2MeSourceProof.h_e62e235b33c1e53765d13c17
    (hH : IsSimplePredictable H F) (X : ℝ≥0 → Ω → ℝ) (s : Set Ω) :
    hH.elementaryIntegral (fun t ↦ s.indicator (X t)) = s.indicator (hH.elementaryIntegral X) :=
  (_root_.Prove2MeSourceProof.h_ef56ad646743a44ff20b8cc8 hH.choose) X s
end IsSimplePredictable

end ProbabilityTheory


