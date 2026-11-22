-- Prove2me | Definitions.Def_LevyStochCalc_Ito_C12Mollify_F000
-- name    : LevyStochCalc_Ito_C12Mollify_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:55:26.848744+00:00
-- url     : https://prove2.me/theorems/0f1143b4-1550-4ec0-8d2d-141a56034cd9
-- title:
--   Source declarations: LevyStochCalc.Ito.C12Mollify
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.C12Mollify. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_C12_F000
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Mollification in time of a function of time and state

For a function `u : ℝ → (Fin n → ℝ) → ℝ` of time and state and a smooth compactly supported bump
`ρ` on `ℝ`, the time mollification `mollifyTime u ρ t x = ∫ r, ρ(r) u(t - r, x) dr` averages `u`
over a window of time of width the outer radius of `ρ`, leaving the state argument untouched. At
a fixed state it is the convolution of the normalised bump with the time section `r ↦ u(r, x)`,
so it inherits the smoothness of the bump in the time variable; it is jointly continuous in time
and state whenever `u` is; and along a family of bumps whose outer radii tend to `0` it converges
to `u` pointwise.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.mollifyTime_apply_eq_convolution` — the time mollification at a
  fixed state is a convolution.
* `LevyStochCalc.Ito.JumpFormula.contDiff_time_mollifyTime` — at a fixed state the time
  mollification is `C^N` in time for every `N`.
* `LevyStochCalc.Ito.JumpFormula.continuous_uncurry_mollifyTime` — the time mollification of a
  jointly continuous function is jointly continuous.
* `LevyStochCalc.Ito.JumpFormula.tendsto_mollifyTime` — pointwise convergence of the time
  mollification along a family of bumps whose outer radii tend to `0`.
* `LevyStochCalc.Ito.JumpFormula.timeDeriv_mollifyTime`,
  `LevyStochCalc.Ito.JumpFormula.gradient_mollifyTime`,
  `LevyStochCalc.Ito.JumpFormula.hessian_mollifyTime` — the time derivative, the gradient and the
  Hessian of the time mollification of a `C^{1,2}` function are the time mollifications of the
  time derivative, the gradient and the Hessian of that function.
-/

open MeasureTheory Filter Topology
open scoped Convolution

namespace LevyStochCalc.Ito.JumpFormula

variable {n : ℕ} {u : ℝ → (Fin n → ℝ) → ℝ}

/-- Mollification in time of `u : ℝ → (Fin n → ℝ) → ℝ` against a bump `ρ` on `ℝ`, normalised for
the volume measure: `mollifyTime u ρ t x = ∫ r, ρ(r) u(t - r, x) dr`. -/
noncomputable def mollifyTime (u : ℝ → (Fin n → ℝ) → ℝ) (ρ : ContDiffBump (0 : ℝ)) (t : ℝ)
    (x : Fin n → ℝ) : ℝ :=
  ∫ r : ℝ, ρ.normed volume r * u (t - r) x
/-- At a fixed state the time mollification is the convolution of the normalised bump with the
time section of `u`. -/
theorem mollifyTime_apply_eq_convolution (ρ : ContDiffBump (0 : ℝ)) (t : ℝ) (x : Fin n → ℝ) :
    mollifyTime u ρ t x
      = (ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun r => u r x) t := by
  simp only [mollifyTime, convolution_lsmul, smul_eq_mul]
/-- The time section `r ↦ u(r, x)` of a jointly continuous function of time and state. -/
theorem continuous_time_section (hu : Continuous (Function.uncurry u)) (x : Fin n → ℝ) :
    Continuous fun r : ℝ => u r x :=
  hu.comp (continuous_id.prodMk continuous_const)
/-- At a fixed state the time mollification of a jointly continuous function is `C^N` in time for
every `N`, the time derivatives falling on the bump. -/
theorem contDiff_time_mollifyTime {N : ℕ∞} (hu : Continuous (Function.uncurry u))
    (ρ : ContDiffBump (0 : ℝ)) (x : Fin n → ℝ) :
    ContDiff ℝ (N : WithTop ℕ∞) fun t => mollifyTime u ρ t x := by
  have hfun : (fun t => mollifyTime u ρ t x)
      = (ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun r => u r x) :=
    funext fun t => mollifyTime_apply_eq_convolution ρ t x
  rw [hfun]
  exact HasCompactSupport.contDiff_convolution_left _ ρ.hasCompactSupport_normed
    ρ.contDiff_normed (continuous_time_section hu x).locallyIntegrable
end LevyStochCalc.Ito.JumpFormula


