-- Prove2me | Definitions.Def_SourceProof_723deac9757f6f9a48c688f4
-- name    : SourceProof_723deac9757f6f9a48c688f4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:10:17.398699+00:00
-- url     : https://prove2.me/theorems/b90026ac-21ab-4416-ba7b-4689bcf9522c
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.measurable_elementaryIntegral

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_Path_RightContinuous_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F002
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F003
import Definitions.Def_SourceProof_28b29a6700445f0b3c267011
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.LocalProperty

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Measurability of the source elementary integral

Finite stopping endpoints are evaluated using the existing usual-filtration path-version
theorem. Integrator integrability and bounds on the integrand are not needed.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

namespace IsSimplePredictable
theorem _root_.Prove2MeSourceProof.h_723deac9757f6f9a48c688f4 {H : ℝ≥0 → Ω → ℝ}
    (hH : IsSimplePredictable H F) (hX : Adapted F X) (hF : F.IsUsual P)
    (hr : HasRightContinuousPaths X P) : Measurable (hH.elementaryIntegral X) :=
  (_root_.Prove2MeSourceProof.h_28b29a6700445f0b3c267011 hH.choose) hX hF hr
end IsSimplePredictable

end ProbabilityTheory


