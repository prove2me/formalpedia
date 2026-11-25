-- Prove2me | Definitions.Def_SourceProof_badb7657c0d57407ebcad38e
-- name    : SourceProof_badb7657c0d57407ebcad38e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:33:24.555011+00:00
-- url     : https://prove2.me/theorems/eb447073-f1b2-49e9-976a-3a5ccc591ccd
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.elementaryIntegralProcess_elementaryIntegralProcess

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F001
import Definitions.Def_SourceProof_0dea52cbb0d6a28823e6ea51
import Definitions.Def_SourceProof_d0b901b94fc3806e9c302bc2
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

theorem _root_.Prove2MeSourceProof.h_badb7657c0d57407ebcad38e
    (hG : IsSimplePredictable G F) (hH : IsSimplePredictable H F) (X : ℝ≥0 → Ω → ℝ) :
    hG.elementaryIntegralProcess (hH.elementaryIntegralProcess X) =
      ((_root_.Prove2MeSourceProof.h_f2413a3b51825efc6a057b76 hG) hH).elementaryIntegralProcess X := by
  funext t
  change hG.elementaryIntegral
    (MeasureTheory.stoppedProcess (hH.elementaryIntegralProcess X) (fun _ ↦ (t : WithTop ℝ≥0))) =
      ((_root_.Prove2MeSourceProof.h_f2413a3b51825efc6a057b76 hG) hH).elementaryIntegral (MeasureTheory.stoppedProcess X (fun _ ↦ (t : WithTop ℝ≥0)))
  rw [← (_root_.Prove2MeSourceProof.h_d0b901b94fc3806e9c302bc2 hH) X (fun _ ↦ (t : WithTop ℝ≥0)),
    (_root_.Prove2MeSourceProof.h_0dea52cbb0d6a28823e6ea51 hG) hH]
end IsSimplePredictable

end ProbabilityTheory


