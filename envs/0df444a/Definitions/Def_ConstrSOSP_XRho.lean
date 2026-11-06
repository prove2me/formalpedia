-- Prove2me | Definitions.Def_ConstrSOSP_XRho
-- name    : ConstrSOSP_XRho
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:58:20.568963+00:00
-- url     : https://prove2.me/theorems/31bdbbf4-f281-4dad-aa9e-f06305b082c2
-- title:
--   Inner region $\mathcal X_\rho$
-- statement:
--   For $0<\rho\le1$, the inner region is $\mathcal X_\rho=\{x\in\mathcal X:\ \operatorname{dist}(x,\partial\mathcal X)\ge\rho\}$.
--
--   **Formalization Note** Written as: $x\in\mathcal X$ and every $y$ with $\|y-x\|<\rho$ (Euclidean) lies in $\mathcal X$. For a closed convex set this is the same condition; the ball form avoids Mathlib's sup-norm distance on `Fin d → ℝ`.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), Appendix B.3, p.85

import Mathlib
import Definitions.Def_ApproxVI_euclNorm
import Definitions.Def_ConstrSOSP_Poly

namespace ConstrSOSP

/-- **The inner region `X_ρ`** (arXiv:2604.02285, 2 Nov 2026, Appendix B.3, p.85: "Fix rational
0 < ρ ≤ 1, and let X_ρ = {x ∈ X : dist(x, ∂X) ≥ ρ}").

`XRho A b ρ` is the set of `x ∈ X = {Ax ≤ b}` such that every `y` with Euclidean `‖y − x‖ < ρ`
lies in `X`.

**Formalization Note** For `x` in the closed convex set `X`, `dist(x, ∂X) ≥ ρ` is equivalent to
the open Euclidean ball of radius `ρ` around `x` lying in `X`; the ball form is used because
Mathlib's `Metric.infDist` on `Fin d → ℝ` is the sup-norm distance. -/
def XRho {m d : ℕ} (A : Fin m → Fin d → ℝ) (b : Fin m → ℝ) (ρ : ℝ) : Set (Fin d → ℝ) :=
  {x | x ∈ Poly A b ∧ ∀ y : Fin d → ℝ, ApproxVI.euclNorm (y - x) < ρ → y ∈ Poly A b}

end ConstrSOSP


