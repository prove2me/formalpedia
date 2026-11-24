-- Prove2me | Definitions.Def_StochLean_ForMathlib_Analysis_LevyAreaRiccati_F000
-- name    : StochLean_ForMathlib_Analysis_LevyAreaRiccati_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T15:02:00.102799+00:00
-- url     : https://prove2.me/theorems/6f177d31-faa9-4a12-9007-291db0d66db5
-- title:
--   StochLean: ForMathlib.Analysis.LevyAreaRiccati F000

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The terminal Riccati coefficients for Levy's stochastic area

These are the actual smooth hyperbolic functions in Protter II.43, for every
real Fourier parameter, including zero and negative parameters. Their signs
on the backward time interval give the deterministic bound on the exponential.
No stochastic-area law or local-martingale conclusion is assumed here.
-/

@[expose] public section

namespace StochLean

noncomputable def levyAreaAlpha (u T t : ℝ) : ℝ := u * Real.tanh (u * (T - t))
noncomputable def levyAreaBeta (u T t : ℝ) : ℝ := -Real.log (Real.cosh (u * (T - t)))
end StochLean


