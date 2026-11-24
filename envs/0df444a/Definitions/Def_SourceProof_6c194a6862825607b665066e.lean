-- Prove2me | Definitions.Def_SourceProof_6c194a6862825607b665066e
-- name    : SourceProof_6c194a6862825607b665066e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:45:33.71681+00:00
-- url     : https://prove2.me/theorems/2d8f88e3-235a-4533-96ec-e0b1714bd87a
-- title:
--   StochLean source theorem: ProbabilityTheory.isContinuousLocalMartingale_const_initial

import Definitions.Def_SourceProof_2c0d4ca99a3f51a9d8eb6cb0
import Definitions.Def_SourceProof_5cb78d7f9a0b64ced0eb04fd

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


theorem _root_.Prove2MeSourceProof.h_6c194a6862825607b665066e [IsFiniteMeasure P]
    [SigmaFiniteFiltration P F] (hZ : Measurable[F 0] Z) :
    IsContinuousLocalMartingale (fun _ : ℝ≥0 ↦ Z) F P := by
  have hcont : ProbabilityTheory.HasContinuousPaths (fun _ : ℝ≥0 ↦ Z) P :=
    ae_of_all _ fun _ ↦ continuous_const
  exact ⟨⟨fun t ↦ hZ.mono (F.mono bot_le) le_rfl, (_root_.Prove2MeSourceProof.h_2c0d4ca99a3f51a9d8eb6cb0 hcont),
    ProbabilityTheory.initialValueLocalizer Z, _root_.Prove2MeSourceProof.h_5cb78d7f9a0b64ced0eb04fd hZ⟩, hcont⟩
end ProbabilityTheory


