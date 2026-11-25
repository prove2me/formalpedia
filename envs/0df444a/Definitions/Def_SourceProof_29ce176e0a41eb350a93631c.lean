-- Prove2me | Definitions.Def_SourceProof_29ce176e0a41eb350a93631c
-- name    : SourceProof_29ce176e0a41eb350a93631c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T21:28:23.147664+00:00
-- url     : https://prove2.me/theorems/d026124b-30ca-5206-81c0-864526b80bcb
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.continuousQuadraticVariation_add

import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticCovariation_ContinuousPart_F000
import Definitions.Def_SourceProof_31d0de13ef1656df97c05a7d

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Quadratic algebra of the existing continuous square component -/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_29ce176e0a41eb350a93631c
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    Indistinguishable (((_root_.Prove2MeSourceProof.h_31d0de13ef1656df97c05a7d hX) hY).continuousQuadraticVariation hF)
      (hX.continuousQuadraticVariation hF +
        (2 : ℝ) • hX.continuousQuadraticCovariation hY hF +
        hY.continuousQuadraticVariation hF) P := by
  apply ae_of_all
  intro ω t
  simp only [ProbabilityTheory.IsSemimartingale.continuousQuadraticCovariation, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring
end IsSemimartingale

end ProbabilityTheory


