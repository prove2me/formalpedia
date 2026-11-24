-- Prove2me | Definitions.Def_SourceProof_619a18497398a378d9ad0e1b
-- name    : SourceProof_619a18497398a378d9ad0e1b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:13:49.150593+00:00
-- url     : https://prove2.me/theorems/9fe016f4-75dc-4301-8df6-ca63d5134bad
-- title:
--   StochLean source theorem: ProbabilityTheory.initialValueLocalizer_monotone

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

theorem _root_.Prove2MeSourceProof.h_619a18497398a378d9ad0e1b (Z : Ω → ℝ) : Monotone (initialValueLocalizer Z) := by
  intro n m hnm ω
  by_cases hn : |Z ω| ≤ (n : ℝ)
  · have hm : |Z ω| ≤ (m : ℝ) := hn.trans (by exact_mod_cast hnm)
    simp [ProbabilityTheory.initialValueLocalizer, hn, hm]
  · simp only [ProbabilityTheory.initialValueLocalizer, hn, ↓reduceIte]
    exact bot_le
end ProbabilityTheory


