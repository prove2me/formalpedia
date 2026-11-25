-- Prove2me | Definitions.Def_SourceProof_ae0266e80e099d3f3f27bbad
-- name    : SourceProof_ae0266e80e099d3f3f27bbad
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:38:51.074251+00:00
-- url     : https://prove2.me/theorems/a08ceaa3-2866-480e-873b-b965ae3718de
-- title:
--   StochLean source theorem: ProbabilityTheory.hasLocallyIntegrableVariation_iff_exists_stopped

import Definitions.Def_StochLean_Probability_Process_FiniteVariation_LocallyIntegrable_F000
import Definitions.Def_SourceProof_19ffdfb9260bf3a7628b85b5
import Definitions.Def_SourceProof_6cfb38f690669c2ac9e645b1

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Locally integrable variation

The local owner is Mathlib's `Locally`, including its positive-lifetime mask.
For variation that mask can be removed without any assumption on the initial
random value: at a zero lifetime the stopped path is constant. The resulting
unmasked criterion is Protter's increasing stopping-time formulation. Adapted
cadlag paths give its literal finite expected stopped-variation criterion,
including the terminal variation when a stopping time is infinite.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

variable {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}

theorem _root_.Prove2MeSourceProof.h_ae0266e80e099d3f3f27bbad :
    HasLocallyIntegrableVariation X F P ↔
      ∃ τ : ℕ → Ω → WithTop ℝ≥0, IsLocalizingSequence F τ P ∧
        ∀ n, HasIntegrableVariation (stoppedProcess X (τ n)) P := by
  constructor
  · rintro ⟨τ, hτ, hX⟩
    exact ⟨τ, hτ, fun n ↦
      (_root_.Prove2MeSourceProof.h_6cfb38f690669c2ac9e645b1 X (τ n)).mp (hX n)⟩
  · rintro ⟨τ, hτ, hX⟩
    exact ⟨τ, hτ, fun n ↦
      (_root_.Prove2MeSourceProof.h_6cfb38f690669c2ac9e645b1 X (τ n)).mpr (hX n)⟩
end ProbabilityTheory


