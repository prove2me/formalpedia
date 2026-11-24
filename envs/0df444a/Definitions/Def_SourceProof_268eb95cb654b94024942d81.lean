-- Prove2me | Definitions.Def_SourceProof_268eb95cb654b94024942d81
-- name    : SourceProof_268eb95cb654b94024942d81
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:01:50.396126+00:00
-- url     : https://prove2.me/theorems/cd9eed19-d969-4127-93b1-33421f82c8ba
-- title:
--   StochLean source theorem: ProbabilityTheory.initialValueLocalizer_isStoppingTime

import Definitions.Def_StochLean_Probability_Process_LocalMartingale_InitialValue_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Initial-value safeguards for local martingales

Any finite F₀-measurable random variable defines a constant Protter local
martingale, even without integrability. Unmasked localization cannot remove
the initial value or make an unbounded initial value bounded.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {Z : Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_268eb95cb654b94024942d81 (hZ : Measurable[F 0] Z) (n : ℕ) :
    IsStoppingTime F (initialValueLocalizer Z n) := by
  intro t
  have hs : MeasurableSet[F t] {ω | |Z ω| ≤ (n : ℝ)} :=
    F.mono bot_le _ (by
      let : MeasurableSpace Ω := F 0
      simpa only [Real.norm_eq_abs] using measurableSet_le hZ.norm measurable_const)
  convert hs.compl using 1
  ext ω
  by_cases h : |Z ω| ≤ (n : ℝ)
  · simp only [ProbabilityTheory.initialValueLocalizer, h, ↓reduceIte, mem_compl_iff, mem_ofPred_eq,
      not_true_eq_false, iff_false]
    exact WithTop.not_top_le_coe t
  · simp only [ProbabilityTheory.initialValueLocalizer, h, ↓reduceIte, mem_compl_iff, mem_ofPred_eq,
      not_false_eq_true]
    exact iff_true_intro bot_le
end ProbabilityTheory


