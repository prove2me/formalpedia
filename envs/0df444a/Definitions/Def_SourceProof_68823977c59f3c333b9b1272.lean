-- Prove2me | Definitions.Def_SourceProof_68823977c59f3c333b9b1272
-- name    : SourceProof_68823977c59f3c333b9b1272
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:28:18.308849+00:00
-- url     : https://prove2.me/theorems/dc8f860d-3698-40e8-acc9-e4705e1084bb
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.elementaryIntegral_zero_integrator

import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F000
import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F002
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F003
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Semimartingales as good integrators

The canonical predicate is zero-sequential continuity of the elementary
integral for uniform convergence in `(t,ω)`. The epsilon/delta source
continuity criterion is proved equivalent. Classical decompositions are not
part of this definition. This file does not select a stochastic integral for
general caglad integrands or a quadratic variation.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

variable {X : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}

namespace IsSimplePredictable

theorem _root_.Prove2MeSourceProof.h_68823977c59f3c333b9b1272
    {H : ℝ≥0 → Ω → ℝ} (hH : IsSimplePredictable H F) :
    hH.elementaryIntegral (0 : ℝ≥0 → Ω → ℝ) = 0 := by
  funext ω
  simp [ProbabilityTheory.IsSimplePredictable.elementaryIntegral, SimplePredictableRep.integral]
end IsSimplePredictable

end ProbabilityTheory


