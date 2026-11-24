-- Prove2me | Definitions.Def_SourceProof_4a6ff19237aa56ae481190c2
-- name    : SourceProof_4a6ff19237aa56ae481190c2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:57:50.130806+00:00
-- url     : https://prove2.me/theorems/f412672f-9b85-4675-a061-fb67be8b51de
-- title:
--   StochLean source theorem: ProbabilityTheory.measurable_denseRunningSupremum

import Definitions.Def_StochLean_Probability_Process_Path_Supremum_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Countable running suprema and pathwise bridges

Generic process-level objects, also used by Brownian path functionals and UCP.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

theorem _root_.Prove2MeSourceProof.h_4a6ff19237aa56ae481190c2 {X : ℝ≥0 → Ω → ℝ}
    (hX : ∀ t, Measurable (X t)) (T : ℝ≥0) :
    Measurable (denseRunningSupremum X T) := by
  apply Measurable.iSup
  intro n
  exact ENNReal.measurable_ofReal.comp (hX (ProbabilityTheory.denseTimeUpTo T n))
end ProbabilityTheory


