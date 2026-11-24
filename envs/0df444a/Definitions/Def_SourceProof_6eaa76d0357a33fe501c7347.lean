-- Prove2me | Definitions.Def_SourceProof_6eaa76d0357a33fe501c7347
-- name    : SourceProof_6eaa76d0357a33fe501c7347
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:45:19.769157+00:00
-- url     : https://prove2.me/theorems/33c3d83a-730f-400f-9f9e-06379c318960
-- title:
--   StochLean source theorem: ProbabilityTheory.FiniteStoppingTime.measurable_right_interval_coefficient

import Definitions.Def_SourceProof_37ebc07daa9ea61d5d2c98e4

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Revealing source coefficients at another stopping time -/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory.FiniteStoppingTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}


theorem _root_.Prove2MeSourceProof.h_6eaa76d0357a33fe501c7347 (τ υ σ : FiniteStoppingTime F) {Z : Ω → ℝ}
    (hZ : Measurable[τ.measurableSpace] Z) :
    Measurable[σ.measurableSpace]
      (fun ω ↦ if τ ω ≤ σ ω ∧ σ ω < υ ω then Z ω else 0) := by
  classical
  have hlt : MeasurableSet[σ.measurableSpace] {ω | σ ω < υ ω} := by
    simpa only [Set.compl_ofPred, WithTop.coe_le_coe, not_le] using
      (υ.isStoppingTime.measurableSet_stopping_time_le σ.isStoppingTime).compl
  have h : Measurable[σ.measurableSpace]
      (fun ω ↦ if σ ω < υ ω then (if τ ω ≤ σ ω then Z ω else 0) else 0) :=
    Measurable.ite hlt ((_root_.Prove2MeSourceProof.h_37ebc07daa9ea61d5d2c98e4 τ) σ hZ) measurable_const
  convert h using 1
  funext ω
  split_ifs <;> tauto
end ProbabilityTheory.FiniteStoppingTime


