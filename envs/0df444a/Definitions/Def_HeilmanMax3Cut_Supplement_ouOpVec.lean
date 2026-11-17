-- Prove2me | Definitions.Def_HeilmanMax3Cut_Supplement_ouOpVec
-- name    : HeilmanMax3Cut_Supplement_ouOpVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:00:25.973064+00:00
-- url     : https://prove2.me/theorems/41b5160e-dd5e-4419-b0ee-73cdb0905485
-- title:
--   Vector-valued Ornstein–Uhlenbeck operator $T_\rho$
-- statement:
--   For $-1<\rho<1$ and a bounded measurable $f:\mathbb R^n\to\mathbb R^k$, the Ornstein–Uhlenbeck operator is
--
--   $$T_\rho f(x)=\int_{\mathbb R^n} f\big(\rho x+y\sqrt{1-\rho^2}\big)\,\gamma_n(y)\,dy,\qquad x\in\mathbb R^n,$$
--
--   where $\gamma_n$ is the standard Gaussian density on $\mathbb R^n$. $T_\rho f(x)$ is the expected value of $f(Y)$ for a Gaussian $Y$ that is $\rho$-correlated with $x$.
--
--   It is the $\mathbb R^k$-valued version of the scalar operator of Part II and enters the noise stability of sphere-valued functions.
--
--   **Formalization Note** $\mathbb R^n$ and $\mathbb R^k$ are Euclidean spaces; the integral is the Bochner integral in $\mathbb R^k$.
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Section 2, p.9

import Mathlib
import Definitions.Def_GaussianPropeller
open MeasureTheory OAI.GaussianPropeller

namespace HeilmanMax3Cut.Supplement

/-- **The vector-valued Ornstein–Uhlenbeck operator `T_ρ`.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Section 2, p.9: "For any
`−1 < ρ < 1` and for any bounded measurable `f : ℝⁿ → ℝᵏ`, let `T_ρ` be the Ornstein–Uhlenbeck
operator `T_ρ f(x) := ∫_{ℝⁿ} f(ρx + y√(1 − ρ²)) γₙ(y) dy` for all `x ∈ ℝⁿ`."

**Formalization Note.** `ℝⁿ` is `OAI.GaussianPropeller.Space n = EuclideanSpace ℝ (Fin n)`, `ℝᵏ` is
`EuclideanSpace ℝ (Fin k)` and `γₙ` is `OAI.GaussianPropeller.gaussian n`; the integral is the
Bochner integral in `ℝᵏ`. The published scalar `HeilmanMax3Cut.ouOp` is the case `k = 1` up to the
identification `ℝ ≅ ℝ¹`; this is the `ℝᵏ`-valued operator of Part I. The theorems apply it only to
bounded measurable `f` and `−1 < ρ < 1`, where the integrand is integrable. -/
noncomputable def ouOpVec (n k : ℕ) (ρ : ℝ) (f : Space n → EuclideanSpace ℝ (Fin k)) (x : Space n) :
    EuclideanSpace ℝ (Fin k) :=
  ∫ y, f (ρ • x + Real.sqrt (1 - ρ ^ 2) • y) ∂(gaussian n)

end HeilmanMax3Cut.Supplement


