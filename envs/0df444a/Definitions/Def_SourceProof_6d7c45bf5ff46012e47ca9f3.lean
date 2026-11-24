-- Prove2me | Definitions.Def_SourceProof_6d7c45bf5ff46012e47ca9f3
-- name    : SourceProof_6d7c45bf5ff46012e47ca9f3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:13:07.339002+00:00
-- url     : https://prove2.me/theorems/dbab2be7-8643-4f84-a4a8-f4967026ebc6
-- title:
--   StochLean source theorem: StochLean.complexCoordinates_apply

import Definitions.Def_StochLean_ForMathlib_Analysis_ComplexCoordinateDerivatives_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Real coordinate derivatives of complex analytic functions

The coordinate map sends (x,y) to x + iy. Real and imaginary components
are handled uniformly by a real continuous linear functional. The two
Hessian indices are ordered, and the second imaginary derivative has its
actual negative sign through I squared.
-/

@[expose] public section

namespace StochLean

@[simp] theorem _root_.Prove2MeSourceProof.h_6d7c45bf5ff46012e47ca9f3 (x : Fin 2 → ℝ) :
    complexCoordinates x = (x 0 : ℂ) + Complex.I * (x 1 : ℂ) := by
  simp [StochLean.complexCoordinates, smul_eq_mul]
end StochLean


