-- Prove2me | Definitions.Def_SourceProof_6cfb38f690669c2ac9e645b1
-- name    : SourceProof_6cfb38f690669c2ac9e645b1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:44:57.06694+00:00
-- url     : https://prove2.me/theorems/e158bb4c-ee17-4436-a451-8c0c20842f98
-- title:
--   StochLean source theorem: ProbabilityTheory.hasIntegrableVariation_stoppedProcess_indicator_pos_iff

import Definitions.Def_SourceProof_4a1a7e20737d275c21c8b8d6

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Stopping and masking integrable variation

Stopping retains the endpoint and does not increase actual total variation.
Usual cadlag adaptedness supplies measurability of the stopped path's total
variation; domination alone would not supply it. The local-property mask at
zero does not affect variation, because a process stopped at zero is constant.
This last statement does not require the initial value to vanish or be integrable.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}

theorem _root_.Prove2MeSourceProof.h_6cfb38f690669c2ac9e645b1
    (X : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0) :
    HasIntegrableVariation (stoppedProcess
      (fun t ↦ {ω | 0 < τ ω}.indicator (X t)) τ) P ↔
      HasIntegrableVariation (stoppedProcess X τ) P := by
  simp only [ProbabilityTheory.HasIntegrableVariation, ProbabilityTheory.HasFiniteTotalVariationPaths, BoundedVariationOn,
    _root_.Prove2MeSourceProof.h_4a1a7e20737d275c21c8b8d6]
end ProbabilityTheory


