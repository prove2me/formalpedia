-- Prove2me | Definitions.Def_SourceProof_cec55a75e8011931c820c0c2
-- name    : SourceProof_cec55a75e8011931c820c0c2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:21:59.262838+00:00
-- url     : https://prove2.me/theorems/3844382e-9b45-4884-ac0f-05e6ba8a28e0
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.complex

import Definitions.Def_StochLean_Probability_Process_Semimartingale_Complex_Basic_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Complex semimartingales are pairs of the existing real semimartingales

This is a coordinate predicate, not another good-integrator construction.
All stochastic integration and bracket owners remain the real ones.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {Z W : ℝ≥0 → Ω → ℂ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_cec55a75e8011931c820c0c2 {X Y : ℝ≥0 → Ω → ℝ}
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) :
    IsComplexSemimartingale (complexProcess X Y) F P := ⟨hX, hY⟩
end IsSemimartingale

end ProbabilityTheory


