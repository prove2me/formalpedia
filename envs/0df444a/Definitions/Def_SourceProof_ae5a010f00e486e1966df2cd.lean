-- Prove2me | Definitions.Def_SourceProof_ae5a010f00e486e1966df2cd
-- name    : SourceProof_ae5a010f00e486e1966df2cd
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:14:29.098267+00:00
-- url     : https://prove2.me/theorems/6d7590a6-f67e-4535-aeee-8ef37aac5e3f
-- title:
--   StochLean source theorem: ProbabilityTheory.initialValueLocalizer_tendsto

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

theorem _root_.Prove2MeSourceProof.h_ae5a010f00e486e1966df2cd (Z : Ω → ℝ) (ω : Ω) :
    Tendsto (fun n ↦ initialValueLocalizer Z n ω) atTop (𝓝 ⊤) := by
  obtain ⟨N, hN⟩ := exists_nat_ge |Z ω|
  refine tendsto_atTop_of_eventually_const (i₀ := N) fun n hn ↦ ?_
  have h : |Z ω| ≤ (n : ℝ) := hN.trans (by exact_mod_cast hn)
  simp [ProbabilityTheory.initialValueLocalizer, h]
end ProbabilityTheory


