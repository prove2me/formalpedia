-- Prove2me | Definitions.Def_SourceProof_6c3d8ad2cd18b3f669ebceea
-- name    : SourceProof_6c3d8ad2cd18b3f669ebceea
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:45:28.666804+00:00
-- url     : https://prove2.me/theorems/911188f8-af9f-4c40-8459-f01b236eab7f
-- title:
--   StochLean source theorem: ProbabilityTheory.IsLocalMartingale.indicator_initial

import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F000
import Definitions.Def_SourceProof_5ac3f4c5fe22f7841ec0a6bc
import Definitions.Def_SourceProof_7e41a7708f0759111a0ce622
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Stopping

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Reducing times and initial-event masking: Protter I.48(a,c,d) -/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X Y : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P]

namespace IsLocalMartingale
omit [IsFiniteMeasure P] in
theorem _root_.Prove2MeSourceProof.h_6c3d8ad2cd18b3f669ebceea (hX : IsLocalMartingale X F P)
    {s : Set Ω} (hs : MeasurableSet[F 0] s) :
    IsLocalMartingale (fun t ↦ s.indicator (X t)) F P := by
  obtain ⟨τ, hτ⟩ := hX.2.2
  refine ⟨fun t ↦ (hX.1 t).indicator (F.mono bot_le s hs), (_root_.Prove2MeSourceProof.h_7e41a7708f0759111a0ce622 hX.2.1) s,
    τ, hτ.1, hτ.2.1, fun n ↦ ?_⟩
  simpa only [stoppedProcess_indicator_comm', Set.indicator_indicator, Set.inter_comm] using
    (_root_.Prove2MeSourceProof.h_5ac3f4c5fe22f7841ec0a6bc (hτ.2.2 n)) hs
end IsLocalMartingale

end ProbabilityTheory


