-- Prove2me | Definitions.Def_SourceProof_bae5ae9701ba5ce704cf231a
-- name    : SourceProof_bae5ae9701ba5ce704cf231a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:12:10.135435+00:00
-- url     : https://prove2.me/theorems/09aab67b-0570-595f-95bd-21d04e6a7f91
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.adapted_elementaryIntegralProcess

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_Path_RightContinuous_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F001
import Definitions.Def_SourceProof_d33983359663d20877640616
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.LocalProperty
import Mathlib.Topology.Algebra.Monoid

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Adaptedness and cadlag paths of the source elementary integral process

The coefficient is revealed only strictly after its left endpoint; before that endpoint
the stopped increment vanishes. Thus no anticipative coefficient measurability is assumed.
Path regularity is pathwise and needs no coefficient bound or integrability hypothesis.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

namespace SimplePredictableRep

end SimplePredictableRep

namespace IsSimplePredictable

variable {H : ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_bae5ae9701ba5ce704cf231a (hH : IsSimplePredictable H F) (hX : Adapted F X)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P) :
    Adapted F (hH.elementaryIntegralProcess X) :=
  (_root_.Prove2MeSourceProof.h_d33983359663d20877640616 hH.choose) hX hF hr
end IsSimplePredictable
end ProbabilityTheory


