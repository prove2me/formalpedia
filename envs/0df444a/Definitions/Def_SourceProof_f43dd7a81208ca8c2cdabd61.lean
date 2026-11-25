-- Prove2me | Definitions.Def_SourceProof_f43dd7a81208ca8c2cdabd61
-- name    : SourceProof_f43dd7a81208ca8c2cdabd61
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:56:24.646752+00:00
-- url     : https://prove2.me/theorems/7ff49153-a4ab-45da-8e5f-3042c1e90c5e
-- title:
--   StochLean source theorem: StochLean.summable_abs_vector_pair_weighted_sq_jumps

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

theorem _root_.Prove2MeSourceProof.h_f43dd7a81208ca8c2cdabd61 (hx : IsCadlagPath x)
    (hs : Summable (fun s : Ioc 0 T ↦ ‖x s - leftLim x s‖ ^ 2))
    {Φ : E → E → ℝ} (hΦ : Continuous (fun p : E × E ↦ Φ p.1 p.2)) :
    Summable (fun s : Ioc 0 T ↦ |Φ (leftLim x s) (x s) * ‖x s - leftLim x s‖ ^ 2|) := by
  obtain ⟨C, _, hC⟩ := _root_.Prove2MeSourceProof.h_522386b326c252eba07b845b hx T hΦ
  apply (hs.mul_left C).of_norm_bounded
  intro s
  simp only [Real.norm_eq_abs, abs_abs, abs_mul,
    abs_of_nonneg (sq_nonneg ‖x s - leftLim x s‖)]
  exact mul_le_mul_of_nonneg_right (hC s ⟨s.2.1.le, s.2.2⟩) (sq_nonneg _)
end StochLean


