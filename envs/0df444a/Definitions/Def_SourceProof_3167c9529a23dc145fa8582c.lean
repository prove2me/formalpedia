-- Prove2me | Definitions.Def_SourceProof_3167c9529a23dc145fa8582c
-- name    : SourceProof_3167c9529a23dc145fa8582c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:26:27.389838+00:00
-- url     : https://prove2.me/theorems/261ca34e-fe82-40b0-9ac1-010fb7106f45
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.stoppedProcess

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_Basic_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Stopping_F000
import Definitions.Def_SourceProof_9627c7bfbc6b93307efa4944
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.LocalProperty

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Stopping source good integrators and semimartingales

The good-integrator proof uses actual source cutoff closure and elementary stopping,
not a classical semimartingale decomposition or a postulated general integral.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_3167c9529a23dc145fa8582c (hX : IsSemimartingale X F P)
    (hF : F.IsUsual P) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    IsSemimartingale (MeasureTheory.stoppedProcess X τ) F P := by
  intro T
  have h := (_root_.Prove2MeSourceProof.h_9627c7bfbc6b93307efa4944 (hX T)) hF hτ
  simpa only [stoppedProcess_stoppedProcess, inf_comm] using h
end IsSemimartingale

end ProbabilityTheory


