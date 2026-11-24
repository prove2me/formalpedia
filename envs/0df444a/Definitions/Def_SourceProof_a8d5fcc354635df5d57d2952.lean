-- Prove2me | Definitions.Def_SourceProof_a8d5fcc354635df5d57d2952
-- name    : SourceProof_a8d5fcc354635df5d57d2952
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:12:58.845602+00:00
-- url     : https://prove2.me/theorems/5ed2411a-4186-42d3-99c4-7425b20703f2
-- title:
--   StochLean source theorem: StochLean.deriv_line_eq_fderiv

import Definitions.Def_StochLean_ForMathlib_Analysis_QuadraticTaylorSlope_F000
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Second-order Taylor remainders along lines in real normed spaces

The scalar Lagrange remainder is applied to the actual line restriction.
No finite-dimensional assumption or globally bounded derivative is needed.
-/

@[expose] public section

open Set

namespace StochLean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}

theorem _root_.Prove2MeSourceProof.h_a8d5fcc354635df5d57d2952 (hf : Differentiable ℝ f) (a v : E) (t : ℝ) :
    deriv (fun r : ℝ ↦ f (a + r • v)) t = fderiv ℝ f (a + t • v) v := by
  have hl : HasDerivAt (fun r : ℝ ↦ a + r • v) v t := by
    simpa only [one_smul, zero_add, Pi.add_def, id_eq] using
      (hasDerivAt_const t a).add ((hasDerivAt_id t).smul_const v)
  exact ((hf (a + t • v)).hasFDerivAt.comp_hasDerivAt t hl).deriv
end StochLean


