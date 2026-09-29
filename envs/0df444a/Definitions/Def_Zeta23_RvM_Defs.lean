-- Prove2me | Definitions.Def_Zeta23_RvM_Defs
-- name    : Zeta23_RvM_Defs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T20:22:12.394609+00:00
-- url     : https://prove2.me/theorems/40e27b3c-0339-4f2c-8d8a-61045c79139f
-- title:
--   Shared vocabulary for the Riemann–von Mangoldt contour
-- statement:
--   Shared vocabulary for the Riemann–von Mangoldt zero-counting argument.
--
--   **Members.**
--   - `GoodHeight T` — the predicate that $T$ is a zero-free ordinate: no nontrivial zero $\rho$ of $\zeta$ has $\operatorname{Im}\rho = T$. Contour heights are always chosen good so that no zero sits on the boundary.
--   - `halfContour F T₁ T₂` — the integral of a function $F:\mathbb C\to\mathbb C$ along the right half-contour $L = [\tfrac12+iT_1 \to 2+iT_1 \to 2+iT_2 \to \tfrac12+iT_2]$, written as three interval integrals (bottom edge rightwards, right side upwards with $ds = i\,dt$, top edge leftwards):
--   $$\int_{1/2}^{2} F(\sigma+iT_1)\,d\sigma \;+\; i\int_{T_1}^{T_2} F(2+it)\,dt \;-\; \int_{1/2}^{2} F(\sigma+iT_2)\,d\sigma.$$
--
--   **Role.** The module documents the route to `Zeta23.RiemannVonMangoldt zetaZeroConfig`: the argument principle for the completed zeta function $\Lambda$ on the rectangle $[-1,2]\times[T_1,T_2]$ at zero-free ordinates is folded onto its right half $L$ by $\Lambda(1-\bar s)=\overline{\Lambda(s)}$, giving $N(T_1,T_2)=\frac1\pi\operatorname{Im}\int_L \Lambda'/\Lambda$; splitting $\Lambda'/\Lambda = \zeta'/\zeta + \Gamma_{\mathbb R}'/\Gamma_{\mathbb R}$ then yields the main term from the $\Gamma$-side (`GammaSide.lean`) and an $O(\log T)$ error from the $\zeta$-side (Backlund). All subsequent `RvM` files state their contour integrals with `halfContour` and their height hypotheses with `GoodHeight`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/RvM/Defs.lean

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_Statement_Seam
import Definitions.Def_Zeta23_Statement_SeamClosed
import Definitions.Def_Zeta23_ZetaReflect

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/RvM/Defs.lean — shared vocabulary for the Riemann–von Mangoldt argument.

Target: Zeta23.RiemannVonMangoldt Zeta23.zetaZeroConfig (Zeta23/Hypotheses.lean), i.e.
  main        : ∃ C T₀, ∀ T ≥ T₀, |N(T,2T) − (T/2π)·ell1 T| ≤ C log T      ([Tit86, Thm 9.4])
  local_count : ∃ A₀ ≥ 1, ∀ t, N(t,t+1] ≤ A₀ log(|t|+3)                      ([Tit86, Thm 9.2]),
                see Zeta23.RvM.zetaZeroConfig_local_count (Zeta23/RvM/LocalCount.lean).
Route for main: argument principle for Λ = completedRiemannZeta
on the rectangle [−1,2]×[T₁,T₂] at zero-free ordinates, folded onto its right half L by
Λ(1−s̄) = conj Λ(s):  N(T₁,T₂) = (1/π)·Im ∫_L Λ'/Λ;  then Λ'/Λ = ζ'/ζ + Γℝ'/Γℝ (Γℝ = Complex.Gammaℝ,
π^{−s/2}Γ(s/2)), and (1/π)·Im ∫_L Γℝ'/Γℝ = ∫_{T₁}^{T₂} μ exactly (μ = Zeta23.mu), whose asymptotic
∫_T^{2T} μ = T·ell1 T/(2π) + O(1/T) is GammaFacts.int_mu. The ζ'/ζ part is O(log T)
(Backlund on the horizontals, |log ζ| ≤ log 3 on σ = 2). Hence: riemannVonMangoldt (hΓ : GammaFacts).
-/

open Complex

noncomputable section

namespace Zeta23.RvM

/-- T is a zero-free ordinate: no nontrivial zero of ζ has Im ρ = T. -/
def GoodHeight (T : ℝ) : Prop := ∀ ρ : ℂ, IsNontrivialZero ρ → ρ.im ≠ T

/-- The right half-contour L = [½+iT₁ → 2+iT₁ → 2+iT₂ → ½+iT₂] integral of F, as three interval
integrals (bottom rightwards, right side upwards with ds = i dt, top leftwards). -/
def halfContour (F : ℂ → ℂ) (T₁ T₂ : ℝ) : ℂ :=
  (∫ σ in (1/2:ℝ)..2, F (σ + T₁ * I)) + (∫ t in T₁..T₂, F (2 + t * I)) * I
    - ∫ σ in (1/2:ℝ)..2, F (σ + T₂ * I)


end Zeta23.RvM


