-- Prove2me | Definitions.Def_StochLean_ForMathlib_Analysis_FiniteCoordinateDerivatives_F000
-- name    : StochLean_ForMathlib_Analysis_FiniteCoordinateDerivatives_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T15:01:58.130837+00:00
-- url     : https://prove2.me/theorems/9d36ef7b-e2e4-4522-a231-8b12627d256c
-- title:
--   StochLean: ForMathlib.Analysis.FiniteCoordinateDerivatives F000

import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Group.Real

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

noncomputable def coordinateDeriv (f : (ι → ℝ) → ℝ) (i : ι) (x : ι → ℝ) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)
noncomputable def coordinateSecondDeriv (f : (ι → ℝ) → ℝ) (i j : ι) (x : ι → ℝ) : ℝ :=
  fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)
end StochLean


