-- Prove2me | Definitions.Def_SourceProof_d306c04c0a492ca797f7a76d
-- name    : SourceProof_d306c04c0a492ca797f7a76d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:13:06.625697+00:00
-- url     : https://prove2.me/theorems/5c46ce8e-0865-42a1-9e20-890b9fc4ba8e
-- title:
--   StochLean source theorem: StochLean.continuous_coordinateSecondDeriv

import Definitions.Def_StochLean_ForMathlib_Analysis_FiniteCoordinateDerivatives_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Coordinate derivatives of finite real vectors

Coordinates are evaluations of Mathlib's Frechet derivatives on the standard
basis. The identities expand the existing linear and bilinear maps exactly.
-/

@[expose] public section

open Finset

namespace StochLean

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem _root_.Prove2MeSourceProof.h_d306c04c0a492ca797f7a76d {f : (ι → ℝ) → ℝ}
    (hf : ContDiff ℝ 2 f) (i j : ι) : Continuous (coordinateSecondDeriv f i j) := by
  have hd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by decide)
  have hH : ContDiff ℝ 0 (fderiv ℝ (fderiv ℝ f)) := hd.fderiv_right (by decide)
  exact ((hH.clm_apply contDiff_const).clm_apply contDiff_const).continuous
end StochLean


