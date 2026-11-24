-- Prove2me | Definitions.Def_SourceProof_86753ecae2d4d5ad377d86c0
-- name    : SourceProof_86753ecae2d4d5ad377d86c0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:45:56.300088+00:00
-- url     : https://prove2.me/theorems/6b4cd5c6-a08d-4f9b-82b5-6429d16969d7
-- title:
--   StochLean source theorem: StochLean.fderiv_apply_eq_sum_coordinateDeriv

import Definitions.Def_StochLean_ForMathlib_Analysis_FiniteCoordinateDerivatives_F000
import Definitions.Def_SourceProof_7d8f5302e992422527b644b2

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

theorem _root_.Prove2MeSourceProof.h_86753ecae2d4d5ad377d86c0 (f : (ι → ℝ) → ℝ) (x v : ι → ℝ) :
    fderiv ℝ f x v = ∑ i, coordinateDeriv f i x * v i :=
  _root_.Prove2MeSourceProof.h_7d8f5302e992422527b644b2 _ _
end StochLean


