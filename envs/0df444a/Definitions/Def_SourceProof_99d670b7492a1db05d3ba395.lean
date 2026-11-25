-- Prove2me | Definitions.Def_SourceProof_99d670b7492a1db05d3ba395
-- name    : SourceProof_99d670b7492a1db05d3ba395
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:27:57.966894+00:00
-- url     : https://prove2.me/theorems/1af1e08c-2941-565a-8bc5-7887a34f51bc
-- title:
--   StochLean source theorem: ProbabilityTheory.SemimartingaleBracketRealization.left_singleton_eq_sq_jump

import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticCovariation_StieltjesRealization_F001
import Definitions.Def_SourceProof_4429ff27e307e8c02b004131

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Actual positive-time atoms of a canonical raw-bracket realization

The Stieltjes measure is that of an indistinguishable increasing version
of the existing raw bracket. Its atom at each positive time is exactly
the squared jump of the original semimartingale, on one common event.
The separate source initial square is not made into a measure atom.
-/

@[expose] public section

open MeasureTheory StochLean
open scoped NNReal

namespace ProbabilityTheory.SemimartingaleBracketRealization

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}
  {hX : IsSemimartingale X F P} {hY : IsSemimartingale Y F P} {hF : F.IsUsual P}

theorem _root_.Prove2MeSourceProof.h_99d670b7492a1db05d3ba395 (D : SemimartingaleBracketRealization hX hY hF) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      (D.left ω).measure {t} = ENNReal.ofReal ((jumpProcess X t ω) ^ 2) := by
  filter_upwards [D.left_eq, (_root_.Prove2MeSourceProof.h_4429ff27e307e8c02b004131 hX) hF] with ω he hj t ht
  rw [StieltjesFunction.measure_singleton]
  apply congrArg ENNReal.ofReal
  have h := hj t
  simpa only [ProbabilityTheory.jumpProcess, Pi.sub_apply, ProbabilityTheory.leftLimitProcess, if_neg (ne_of_gt ht), he] using h
end ProbabilityTheory.SemimartingaleBracketRealization


