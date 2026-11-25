-- Prove2me | Definitions.Def_SourceProof_56c71dd2079e6b44a7dc4950
-- name    : SourceProof_56c71dd2079e6b44a7dc4950
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:30:58.939926+00:00
-- url     : https://prove2.me/theorems/bcdd292d-08a6-5275-b124-b73b97d41359
-- title:
--   StochLean source theorem: StochLean.summable_abs_frechet_first_order_jump_remainders

import Definitions.Def_SourceProof_41764b24f2eac06df69d99ab
import Definitions.Def_SourceProof_4d7fc7190a3d02a61bd44d4d

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Absolute vector Taylor jump series from square-summable jump norms

Local compact bounds control the actual first- and second-order corrections.
The original path is not assumed to have finite variation.
-/

@[expose] public section

open Set Function ProbabilityTheory
open scoped NNReal

namespace StochLean

variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E] {x : ℝ≥0 → E} {T : ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_56c71dd2079e6b44a7dc4950 [NormedSpace ℝ E]
    (hx : IsCadlagPath x) (hs : Summable (fun s : Ioc 0 T ↦ ‖x s - leftLim x s‖ ^ 2))
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) :
    Summable (fun s : Ioc 0 T ↦
      |f (x s) - f (leftLim x s) - fderiv ℝ f (leftLim x s) (x s - leftLim x s)|) := by
  have hd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by decide)
  have hR := (_root_.Prove2MeSourceProof.h_4d7fc7190a3d02a61bd44d4d hx hs hf).of_abs
  have hL := (_root_.Prove2MeSourceProof.h_41764b24f2eac06df69d99ab hx hs
    (hd.continuous_fderiv (by decide))).of_abs
  have hsum := hR.add (hL.mul_left (1 / 2 : ℝ))
  have he : (fun s : Ioc 0 T ↦ StochLean.frechetSecondOrderRemainder f (leftLim x s) (x s) +
      (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) (leftLim x s)
        (x s - leftLim x s) (x s - leftLim x s)) =
      fun s : Ioc 0 T ↦ f (x s) - f (leftLim x s) -
        fderiv ℝ f (leftLim x s) (x s - leftLim x s) := by
    funext s
    unfold StochLean.frechetSecondOrderRemainder
    ring
  rw [he] at hsum
  exact hsum.abs
end StochLean


