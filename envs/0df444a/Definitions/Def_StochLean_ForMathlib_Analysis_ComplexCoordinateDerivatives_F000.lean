-- Prove2me | Definitions.Def_StochLean_ForMathlib_Analysis_ComplexCoordinateDerivatives_F000
-- name    : StochLean_ForMathlib_Analysis_ComplexCoordinateDerivatives_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T15:01:59.999548+00:00
-- url     : https://prove2.me/theorems/00a3c94f-1b85-49be-b2c3-5e789b4ece50
-- title:
--   StochLean: ForMathlib.Analysis.ComplexCoordinateDerivatives F000

import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Normed.Group.Real

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

noncomputable def complexCoordinates : (Fin 2 → ℝ) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (ContinuousLinearMap.proj 0) +
    Complex.I • Complex.ofRealCLM.comp (ContinuousLinearMap.proj 1)
end StochLean


