-- Prove2me | Definitions.Def_Zeta23_RvM_GammaSide
-- name    : Zeta23_RvM_GammaSide
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T20:22:41.197395+00:00
-- url     : https://prove2.me/theorems/d8dcccc5-9d71-4f7c-ac3e-545da7429ff5
-- title:
--   Setup for the $\Gamma$-factor side of the folded contour
-- statement:
--   Setup definition for the $\Gamma$-factor side of the Riemann–von Mangoldt argument: `rightHalfPlane` is the open right half-plane
--   $$\{s\in\mathbb C : 0<\operatorname{Re} s\}.$$
--
--   **Role.** The module `Zeta23/RvM/GammaSide.lean` proves that the $\Gamma$-factor contribution to the folded contour is *exactly* the paper's archimedean density integral: $\frac1\pi\operatorname{Im}\int_L \Gamma_{\mathbb R}'/\Gamma_{\mathbb R}\,ds=\int_{T_1}^{T_2}\mu(t)\,dt$ for $0<T_1$, where $\Gamma_{\mathbb R}(s)=\pi^{-s/2}\Gamma(s/2)$ and $\mu$ = `Zeta23.mu`. The half-plane is the domain on which $\Gamma_{\mathbb R}'/\Gamma_{\mathbb R}$ is holomorphic, so that Cauchy–Goursat on $[\tfrac12,2]\times[T_1,T_2]$ can move the contour $L$ to the critical-line segment, where $\operatorname{Re}\,\Gamma_{\mathbb R}'/\Gamma_{\mathbb R}(\tfrac12+it)=\pi\,\mu(t)$. This supplies the main term $\int_T^{2T}\mu$ of the zero count $N(T,2T)$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/RvM/GammaSide.lean

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
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
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
import Definitions.Def_Zeta23_RvM_Defs
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
Zeta23/RvM/GammaSide.lean — the Γ-factor side of the folded contour is
EXACTLY the paper's ∫μ:  (1/π)·Im ∫_L Γℝ'/Γℝ ds = ∫_{T₁}^{T₂} μ(t) dt  for 0 < T₁,
because Γℝ'/Γℝ is holomorphic on Re s > 0 (Cauchy–Goursat on [½,2]×[T₁,T₂] moves L to the critical-line
segment) and Re Γℝ'/Γℝ(½+it) = ½ Re ψ(¼+it/2) − ½ log π = π·μ(t)  (Γℝ(s) = π^{−s/2}Γ(s/2), μ = Zeta23.mu).
-/

open Complex MeasureTheory Set
open scoped Interval

noncomputable section

namespace Zeta23.RvM

/-- the open right half-plane -/
def rightHalfPlane : Set ℂ := {s : ℂ | 0 < s.re}









/-! ### helpers for the assembly -/



end Zeta23.RvM


