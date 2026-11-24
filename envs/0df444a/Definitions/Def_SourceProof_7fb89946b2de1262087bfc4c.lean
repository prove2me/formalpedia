-- Prove2me | Definitions.Def_SourceProof_7fb89946b2de1262087bfc4c
-- name    : SourceProof_7fb89946b2de1262087bfc4c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:45:20.944814+00:00
-- url     : https://prove2.me/theorems/c5ad6ef2-3283-4e1c-852d-1dab51570f11
-- title:
--   StochLean source theorem: StochLean.second_deriv_line_eq_fderiv

import Definitions.Def_SourceProof_a8d5fcc354635df5d57d2952

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

theorem _root_.Prove2MeSourceProof.h_7fb89946b2de1262087bfc4c (hf : ContDiff ℝ 2 f) (a v : E) (t : ℝ) :
    deriv (deriv (fun r : ℝ ↦ f (a + r • v))) t =
      fderiv ℝ (fderiv ℝ f) (a + t • v) v v := by
  have hd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by decide)
  have hl : HasDerivAt (fun r : ℝ ↦ a + r • v) v t := by
    simpa only [one_smul, zero_add, Pi.add_def, id_eq] using
      (hasDerivAt_const t a).add ((hasDerivAt_id t).smul_const v)
  have he : deriv (fun r : ℝ ↦ f (a + r • v)) =
      fun r ↦ fderiv ℝ f (a + r • v) v :=
    funext (_root_.Prove2MeSourceProof.h_a8d5fcc354635df5d57d2952 (hf.differentiable (by decide)) a v)
  rw [he]
  have hD := ((hd.differentiable (by decide)) (a + t • v)).hasFDerivAt
  have hD' : HasDerivAt (fun r : ℝ ↦ fderiv ℝ f (a + r • v))
      (fderiv ℝ (fderiv ℝ f) (a + t • v) v) t := hD.comp_hasDerivAt t hl
  have h := hD'.clm_apply (hasDerivAt_const t v)
  simpa only [map_zero, add_zero] using h.deriv
end StochLean


