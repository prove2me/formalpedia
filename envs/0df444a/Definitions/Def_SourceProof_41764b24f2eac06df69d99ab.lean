-- Prove2me | Definitions.Def_SourceProof_41764b24f2eac06df69d99ab
-- name    : SourceProof_41764b24f2eac06df69d99ab
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:20:12.111626+00:00
-- url     : https://prove2.me/theorems/46e900d2-8d3a-432c-a51d-d5a03925842f
-- title:
--   StochLean source theorem: StochLean.summable_abs_cadlag_bilinear_jumps

import Definitions.Def_StochLean_ForMathlib_Analysis_FrechetTaylorCoefficient_F000
import Definitions.Def_SourceProof_522386b326c252eba07b845b

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

theorem _root_.Prove2MeSourceProof.h_41764b24f2eac06df69d99ab [NormedSpace ℝ E] (hx : IsCadlagPath x)
    (hs : Summable (fun s : Ioc 0 T ↦ ‖x s - leftLim x s‖ ^ 2))
    {L : E → E →L[ℝ] E →L[ℝ] ℝ} (hL : Continuous L) :
    Summable (fun s : Ioc 0 T ↦
      |L (leftLim x s) (x s - leftLim x s) (x s - leftLim x s)|) := by
  have hn : Continuous (fun a : E ↦ ‖L a‖) := by
    simpa only [Function.comp_def] using
      (continuous_norm (E := E →L[ℝ] E →L[ℝ] ℝ)).comp hL
  have hp : Continuous (fun p : E × E ↦ ‖L p.1‖) := by
    simpa only [Function.comp_def] using hn.comp continuous_fst
  obtain ⟨C, _, hC⟩ := _root_.Prove2MeSourceProof.h_522386b326c252eba07b845b hx T
    (Φ := fun a _ ↦ ‖L a‖) hp
  apply (hs.mul_left C).of_norm_bounded
  intro s
  simp only [Real.norm_eq_abs, abs_abs]
  have hc : ‖L (leftLim x s)‖ ≤ C := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (L (leftLim x s)))] using
      hC s ⟨s.2.1.le, s.2.2⟩
  calc
    _ ≤ ‖L (leftLim x s) (x s - leftLim x s)‖ * ‖x s - leftLim x s‖ :=
      (L (leftLim x s) (x s - leftLim x s)).le_opNorm _
    _ ≤ (‖L (leftLim x s)‖ * ‖x s - leftLim x s‖) * ‖x s - leftLim x s‖ :=
      mul_le_mul_of_nonneg_right ((L (leftLim x s)).le_opNorm _) (norm_nonneg _)
    _ ≤ (C * ‖x s - leftLim x s‖) * ‖x s - leftLim x s‖ := by gcongr
    _ = _ := by ring
end StochLean


