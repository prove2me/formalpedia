-- Prove2me | Definitions.Def_SourceProof_3485556bf52a24d375b7ad3f
-- name    : SourceProof_3485556bf52a24d375b7ad3f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:13:58.934664+00:00
-- url     : https://prove2.me/theorems/b0f39566-2628-5cf7-a23a-fa19469de78a
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.quadraticVariation_add

import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticCovariation_F000
import Definitions.Def_SourceProof_31d0de13ef1656df97c05a7d

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Quadratic identities for the canonical raw square bracket -/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_3485556bf52a24d375b7ad3f
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    Indistinguishable (((_root_.Prove2MeSourceProof.h_31d0de13ef1656df97c05a7d hX) hY).quadraticVariation hF)
      (hX.quadraticVariation hF + (2 : ℝ) • hX.quadraticCovariation hY hF +
        hY.quadraticVariation hF) P := by
  apply ae_of_all
  intro ω t
  simp only [ProbabilityTheory.IsSemimartingale.quadraticCovariation, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring
end IsSemimartingale

end ProbabilityTheory


