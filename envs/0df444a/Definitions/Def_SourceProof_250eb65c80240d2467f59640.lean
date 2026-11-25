-- Prove2me | Definitions.Def_SourceProof_250eb65c80240d2467f59640
-- name    : SourceProof_250eb65c80240d2467f59640
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:33:07.271283+00:00
-- url     : https://prove2.me/theorems/5ad39368-a8ff-5ecb-8161-75121c6eca2c
-- title:
--   StochLean source theorem: ProbabilityTheory.HasCagladPaths.cutoffIntegrand

import Definitions.Def_StochLean_Probability_Process_Stopping_Integrand_F000
import Definitions.Def_SourceProof_44d3901c783fecbaee68385f

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Common-event cutoff regularity and invariance -/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {H K : ℝ≥0 → Ω → ℝ}

namespace HasCagladPaths
theorem _root_.Prove2MeSourceProof.h_250eb65c80240d2467f59640 (hH : HasCagladPaths H P)
    (τ : Ω → WithTop ℝ≥0) : HasCagladPaths (cutoffIntegrand H τ) P := by
  filter_upwards [hH] with ω hω
  exact _root_.Prove2MeSourceProof.h_44d3901c783fecbaee68385f (H := fun t (_ : Unit) ↦ H t ω)
    (fun _ ↦ hω) (fun _ ↦ τ ω) ()
end HasCagladPaths

end ProbabilityTheory


