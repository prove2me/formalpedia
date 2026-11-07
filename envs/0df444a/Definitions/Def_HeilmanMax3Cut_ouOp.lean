-- Prove2me | Definitions.Def_HeilmanMax3Cut_ouOp
-- name    : HeilmanMax3Cut_ouOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:27:06.026654+00:00
-- url     : https://prove2.me/theorems/b48a8f0a-79b0-4f97-831e-b7f28409625a
-- title:
--   The Ornstein–Uhlenbeck operator $T_\rho$
-- statement:
--   Let $\gamma_n$ be the standard Gaussian probability measure on $\mathbb R^n$. For a bounded measurable $f:\mathbb R^n\to\mathbb R$ and $-1<\rho<1$,
--
--   $$T_\rho f(x)=\int_{\mathbb R^n} f\bigl(\rho x+\sqrt{1-\rho^2}\,y\bigr)\,d\gamma_n(y),\qquad x\in\mathbb R^n .$$
--
--   $T_\rho f(x)$ is the expectation of $f(Y)$ for $Y$ a standard Gaussian $\rho$-correlated with $X=x$.
--
--   **Formalization Note** The paper states $T_\rho$ for vector-valued $f$; Part II applies it only to indicator functions, so the scalar version is used. The formula is evaluated for every real $\rho$.
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Section 2, p.9

import Mathlib
import Definitions.Def_GaussianPropeller
open MeasureTheory OAI.GaussianPropeller

namespace HeilmanMax3Cut

/-- **The Ornstein–Uhlenbeck operator `T_ρ`.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Section 2, p.9:
`T_ρ f(x) := ∫_{ℝⁿ} f(ρx + y√(1 − ρ²)) γₙ(y) dy` for all `x ∈ ℝⁿ`, where `γₙ` is the standard
Gaussian measure on `ℝⁿ`.

**Formalization Note.** `ℝⁿ` is `OAI.GaussianPropeller.Space n = EuclideanSpace ℝ (Fin n)` and `γₙ`
is `OAI.GaussianPropeller.gaussian n` (the standard Gaussian measure). The paper states the operator
for bounded measurable `f : ℝⁿ → ℝᵏ` and `−1 < ρ < 1`; Part II applies it to indicator functions
(52), so the scalar-valued version is used. -/
noncomputable def ouOp (n : ℕ) (ρ : ℝ) (f : Space n → ℝ) (x : Space n) : ℝ :=
  ∫ y, f (ρ • x + Real.sqrt (1 - ρ ^ 2) • y) ∂(gaussian n)

end HeilmanMax3Cut


