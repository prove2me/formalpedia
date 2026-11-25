-- Prove2me | Definitions.Def_SourceProof_9d2aae30149707576aa509f3
-- name    : SourceProof_9d2aae30149707576aa509f3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:45:09.877821+00:00
-- url     : https://prove2.me/theorems/c5dfd3af-fab2-4941-816c-c26c2fc34ef4
-- title:
--   StochLean source theorem: ProbabilityTheory.FiniteStoppingTime.measurable_interval_coefficient

import Definitions.Def_SourceProof_013463e4574b0455441609f2

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Revealing a stopping-time coefficient strictly after its stopping time -/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory.FiniteStoppingTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

theorem _root_.Prove2MeSourceProof.h_9d2aae30149707576aa509f3 (τ σ : FiniteStoppingTime F) {Z : Ω → ℝ}
    (hZ : Measurable[τ.measurableSpace] Z) (t : ℝ≥0) :
    Measurable[F t] (fun ω ↦ if τ ω < t ∧ t ≤ σ ω then Z ω else 0) := by
  classical
  have hge : MeasurableSet[F t] {ω | t ≤ σ ω} := by
    simpa only [WithTop.coe_le_coe] using σ.isStoppingTime.measurableSet_ge t
  have h : Measurable[F t]
      (fun ω ↦ if t ≤ σ ω then (if τ ω < t then Z ω else 0) else 0) :=
    Measurable.ite hge ((_root_.Prove2MeSourceProof.h_013463e4574b0455441609f2 τ) hZ t) measurable_const
  convert h using 1
  funext ω
  split_ifs <;> tauto
end ProbabilityTheory.FiniteStoppingTime


