-- Prove2me | Definitions.Def_SourceProof_2ea59af0c9ba6765e1c4dab1
-- name    : SourceProof_2ea59af0c9ba6765e1c4dab1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:21:02.775801+00:00
-- url     : https://prove2.me/theorems/c65de5a8-bd5a-43bb-8fec-d2e4e4d42759
-- title:
--   StochLean source theorem: ProbabilityTheory.measurable_denseWindowOscillation

import Definitions.Def_StochLean_Probability_Process_Path_CadlagWindowOscillation_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Measurable two-time short-window oscillations

The envelope uses two points of the existing clipped dense grid and an actual
order and strict-width guard. Countability makes it measurable. Two right-side
approximating sequences recover every strict window of a right-continuous
path; doubling a positive width also covers a closed-width window. Cadlag
compact boundedness proves finiteness before the real-valued bridge is used.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

theorem _root_.Prove2MeSourceProof.h_2ea59af0c9ba6765e1c4dab1 {X : ℝ≥0 → Ω → ℝ}
    (hX : ∀ t, Measurable (X t)) (T δ : ℝ≥0) :
    Measurable (denseWindowOscillation X T δ) := by
  apply Measurable.iSup
  intro i
  apply Measurable.iSup
  intro j
  by_cases h : ProbabilityTheory.denseTimeUpTo T i ≤ ProbabilityTheory.denseTimeUpTo T j ∧
      ProbabilityTheory.denseTimeUpTo T j < ProbabilityTheory.denseTimeUpTo T i + δ
  · simp only [if_pos h]
    exact ENNReal.measurable_ofReal.comp ((hX _).sub (hX _)).norm
  · simp only [if_neg h]
    exact measurable_const
end ProbabilityTheory


