-- Prove2me | Definitions.Def_SourceProof_0dea52cbb0d6a28823e6ea51
-- name    : SourceProof_0dea52cbb0d6a28823e6ea51
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:21:51.821639+00:00
-- url     : https://prove2.me/theorems/57bcb7ee-9f2f-55ad-8063-21d636ac7849
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.elementaryIntegral_elementaryIntegralProcess

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F001
import Definitions.Def_SourceProof_92f98353d1ecfc763009098e
import Definitions.Def_SourceProof_b988128ba11f468cb1bbadce
import Definitions.Def_SourceProof_f2413a3b51825efc6a057b76
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Predictable
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Associativity of source elementary integration

Actual common stopping partitions reduce the proof to the integral increment
on one cell. Both the initial coefficient product and every repeated endpoint
are retained. The integrator is arbitrary; no semimartingale premise is used.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

namespace SimplePredictableRep

end SimplePredictableRep

namespace IsSimplePredictable

variable {G H : ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_0dea52cbb0d6a28823e6ea51
    (hG : IsSimplePredictable G F) (hH : IsSimplePredictable H F) (X : ℝ≥0 → Ω → ℝ) :
    hG.elementaryIntegral (hH.elementaryIntegralProcess X) = ((_root_.Prove2MeSourceProof.h_f2413a3b51825efc6a057b76 hG) hH).elementaryIntegral X := by
  have h := (_root_.Prove2MeSourceProof.h_b988128ba11f468cb1bbadce hG.choose) hH.choose X
  change hG.choose.integral (hH.choose.integralProcess X) = _
  refine h.trans (_root_.Prove2MeSourceProof.h_92f98353d1ecfc763009098e _ ((_root_.Prove2MeSourceProof.h_f2413a3b51825efc6a057b76 hG) hH) ?_ X)
  rw [hG.choose_spec, hH.choose_spec]
end IsSimplePredictable

end ProbabilityTheory


