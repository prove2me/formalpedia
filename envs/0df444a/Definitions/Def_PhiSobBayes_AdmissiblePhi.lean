-- Prove2me | Definitions.Def_PhiSobBayes_AdmissiblePhi
-- name    : PhiSobBayes_AdmissiblePhi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T23:05:02.960961+00:00
-- url     : https://prove2.me/theorems/3b269816-5c15-403d-8d32-b152f2a2a006
-- title:
--   Admissible $\Phi$: smooth on $J$ with $\Phi''>0$ and $1/\Phi''$ concave
-- statement:
--   Let $J\subseteq\mathbb R$ be an open interval. A function $\Phi:J\to\mathbb R$ is **admissible** if
--
--   1. $\Phi$ is smooth ($C^\infty$) on $J$,
--   2. $\Phi''(z)>0$ for every $z\in J$, and
--   3. $z\mapsto 1/\Phi''(z)$ is concave on $J$.
--
--   These are the hypotheses on $\Phi$ in Chafaï's $\Phi$-Sobolev inequalities and in Theorem 3.1. The two main examples are $\Phi(z)=(z-1)^2$ on $J=\mathbb R$ (Poincaré) and $\Phi(z)=z\log z$ on $J=(0,\infty)$ (log-Sobolev).
--
--   **Formalization Note** $\Phi$ is a total function $\mathbb R\to\mathbb R$; only its values on $J$ matter. Since $J$ is open, `deriv Φ` and `deriv (deriv Φ)` at points of $J$ are the derivatives of $\Phi|_J$. Smoothness is `ContDiffOn ℝ ∞` ($C^\infty$, not analyticity).
-- source:
--   Li–Zadik, Functional inequalities from the fundamental limits of Bayesian estimation, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Section 1, p.3 (PDF 3); Theorem 3.1, p.15 (PDF 15)

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal ContDiff

namespace PhiSobBayes

/-- `Φ` is **admissible on `J`**: smooth on `J`, with `Φ″ > 0` and `1/Φ″` concave on `J`.

Li–Zadik, *Functional inequalities from the fundamental limits of Bayesian estimation*, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Section 1, p.3 (PDF 3): "let 𝐽 ⊆ ℝ be an open interval and let Φ : 𝐽 → ℝ be smooth with
Φ′′ > 0 and 1/Φ′′ concave"; the same hypotheses in Theorem 3.1, p.15 (PDF 15).

**Formalization Note** `Φ` is a total function `ℝ → ℝ`, and only its values on `J` matter. For the
open intervals `J` of the paper, `deriv Φ` and `deriv (deriv Φ)` at a point of `J` are the first and
second derivatives of `Φ|_J`. "Smooth" is `ContDiffOn ℝ ∞` (`∞` is `C^∞`; `⊤` would be analyticity).
`ConcaveOn ℝ J` includes the convexity of `J`. -/
def AdmissiblePhi (J : Set ℝ) (Φ : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ∞ Φ J ∧ (∀ z ∈ J, 0 < deriv (deriv Φ) z) ∧
    ConcaveOn ℝ J (fun z => (deriv (deriv Φ) z)⁻¹)

end PhiSobBayes


