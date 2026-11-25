-- Prove2me | Definitions.Def_SourceProof_0339642eaaa29ff45e7162b6
-- name    : SourceProof_0339642eaaa29ff45e7162b6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:56:13.513869+00:00
-- url     : https://prove2.me/theorems/3f66463e-bd60-4812-9a49-88094337cd23
-- title:
--   StochLean source theorem: StochLean.stieltjesContinuousPart_add_jumpPart

import Definitions.Def_StochLean_Analysis_PathVariation_StieltjesContinuousPart_F000
import Definitions.Def_SourceProof_2f8153518021639b8e8e83d5
import Definitions.Def_SourceProof_49c549aa0a44f9f3d29251ef
import Definitions.Def_SourceProof_561d7fc50af0bdd1f0a29ad5
import Definitions.Def_SourceProof_6fcc1c928f053fa880b8a3cf
import Definitions.Def_SourceProof_8b8684e748d5e31b03d0af2c

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Continuous and jump parts of an increasing right-continuous path

Both parts start at zero and use the original Stieltjes measure. Continuity of
the diffuse part follows from the singleton/left-jump formula, including the
bottom endpoint. The original initial value remains a separate term.
-/

@[expose] public section

open MeasureTheory Set Function
open scoped NNReal ENNReal

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_0339642eaaa29ff45e7162b6 (f : StieltjesFunction ℝ≥0) (t : ℝ≥0) :
    stieltjesContinuousPart f t + stieltjesJumpPart f t = f t - f 0 := by
  have hsum := congrArg (fun μ : Measure ℝ≥0 ↦ μ.real (Iic t))
    (_root_.Prove2MeSourceProof.h_2f8153518021639b8e8e83d5 f.measure)
  rw [measureReal_add_apply
    (_root_.Prove2MeSourceProof.h_6fcc1c928f053fa880b8a3cf f (_root_.Prove2MeSourceProof.h_49c549aa0a44f9f3d29251ef f.measure) t).ne
    (_root_.Prove2MeSourceProof.h_6fcc1c928f053fa880b8a3cf f (_root_.Prove2MeSourceProof.h_8b8684e748d5e31b03d0af2c f.measure) t).ne] at hsum
  change (StochLean.pointAtomicPart f.measure).real (Iic t) +
    (StochLean.pointDiffusePart f.measure).real (Iic t) = _ at hsum
  simp only [measureReal_def] at hsum
  rw [_root_.Prove2MeSourceProof.h_561d7fc50af0bdd1f0a29ad5,
    ENNReal.toReal_ofReal
      (show 0 ≤ f t - f 0 from sub_nonneg.mpr (f.mono (show (0 : ℝ≥0) ≤ t from bot_le)))] at hsum
  exact (add_comm _ _).trans hsum
end StochLean


