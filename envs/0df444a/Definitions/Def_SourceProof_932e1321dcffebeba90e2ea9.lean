-- Prove2me | Definitions.Def_SourceProof_932e1321dcffebeba90e2ea9
-- name    : SourceProof_932e1321dcffebeba90e2ea9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:34:42.978747+00:00
-- url     : https://prove2.me/theorems/cb8b5489-eaf4-4fb9-b662-1557150144c8
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.hasCadlagPaths_elementaryIntegralProcess

import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F001
import Definitions.Def_SourceProof_3bfb9ef0d258afe6eedb13c5
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
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

theorem _root_.Prove2MeSourceProof.h_932e1321dcffebeba90e2ea9 (hH : IsSimplePredictable H F)
    (hX : HasCadlagPaths X P) : HasCadlagPaths (hH.elementaryIntegralProcess X) P :=
  (_root_.Prove2MeSourceProof.h_3bfb9ef0d258afe6eedb13c5 hH.choose) hX
end IsSimplePredictable
end ProbabilityTheory


