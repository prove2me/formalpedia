-- Prove2me | Definitions.Def_SourceProof_aa100ce908969cff7fac9e9d
-- name    : SourceProof_aa100ce908969cff7fac9e9d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:13:06.888888+00:00
-- url     : https://prove2.me/theorems/94204195-cb3a-4676-92c0-55a3dfa32a77
-- title:
--   StochLean source theorem: StochLean.contDiff_coordinateDeriv

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

theorem _root_.Prove2MeSourceProof.h_aa100ce908969cff7fac9e9d {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (i : ι) :
    ContDiff ℝ 1 (coordinateDeriv f i) := by
  have hd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by decide)
  exact hd.clm_apply contDiff_const
end StochLean


