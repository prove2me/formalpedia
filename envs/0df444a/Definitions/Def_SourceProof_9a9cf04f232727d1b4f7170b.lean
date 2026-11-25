-- Prove2me | Definitions.Def_SourceProof_9a9cf04f232727d1b4f7170b
-- name    : SourceProof_9a9cf04f232727d1b4f7170b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:44:48.615247+00:00
-- url     : https://prove2.me/theorems/29353326-eded-4aa3-912b-cc21ce4458d1
-- title:
--   StochLean source theorem: StochLean.second_fderiv_apply_eq_sum_coordinateSecondDeriv

import Definitions.Def_StochLean_ForMathlib_Analysis_FiniteCoordinateDerivatives_F000
import Definitions.Def_SourceProof_70e19260acc6d4f0931811a5

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

theorem _root_.Prove2MeSourceProof.h_9a9cf04f232727d1b4f7170b
    (f : (ι → ℝ) → ℝ) (x v w : ι → ℝ) :
    fderiv ℝ (fderiv ℝ f) x v w = ∑ i, ∑ j, coordinateSecondDeriv f i j x * v i * w j :=
  _root_.Prove2MeSourceProof.h_70e19260acc6d4f0931811a5 _ _ _
end StochLean


