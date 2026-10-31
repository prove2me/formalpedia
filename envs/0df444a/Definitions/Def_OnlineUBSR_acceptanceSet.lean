-- Prove2me | Definitions.Def_OnlineUBSR_acceptanceSet
-- name    : OnlineUBSR_acceptanceSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:18:14.644271+00:00
-- url     : https://prove2.me/theorems/2c93f076-a2de-43c1-8885-f3a197d6fad9
-- title:
--   Acceptance set $\mathcal A=\{Y\in L^\infty:\mathbb E[\ell(-Y)]\le\lambda\}$
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space, $\ell:\mathbb R\to\mathbb R$ a loss function and $\lambda\in\mathbb R$ a risk level. The **acceptance set** is
--
--   $$
--   \mathcal A=\{\,Y\in L^\infty:\ \mathbb E[\ell(-Y)]\le\lambda\,\},
--   $$
--
--   the set of bounded random variables whose expected loss is at most $\lambda$. A position is acceptable when its expected loss does not exceed the risk level; utility-based shortfall risk is the least cash that makes a position acceptable.
--
--   **Formalization Note** $Y\in L^\infty$ is `MemLp Y ⊤ μ` (a.e. strongly measurable and essentially bounded). The expectation is the Bochner integral; for $Y\in L^\infty$ and a convex (hence continuous) $\ell$ the integrand is bounded a.s., so it is the true expectation. Convexity of $\ell$ and the position of $\lambda$ are hypotheses of the theorems, not part of the definition.
-- source:
--   Hegde, Menon, Prashanth & Jagannathan, Online Estimation and Optimization of Utility-Based Shortfall Risk, arXiv:2111.08805v3, §2, eq. (1), p.3

import Mathlib

open MeasureTheory

namespace OnlineUBSR

/-- **The acceptance set of utility-based shortfall risk.**
Hegde, Menon, Prashanth & Jagannathan, arXiv:2111.08805v3, §2, (1), p.3: "Let X be a random
variable, and ℓ(·) be a convex loss function. Let λ be a pre-specified 'risk-level' parameter
[…]. We first define an acceptance set as follows: A := {X ∈ L∞ : E[ℓ(−X)] ≤ λ}, (1) where L∞
represents the set of bounded random variables."

`acceptanceSet μ ℓ lam` is the set of random variables `Y : Ω → ℝ` that lie in `L∞(μ)` and
satisfy `∫ ℓ(−Y) dμ ≤ lam`.

**Formalization Note.** "Bounded random variable" is `MemLp Y ⊤ μ`: `Y` is a.e. strongly
measurable and essentially bounded. The expectation is the Bochner integral; for `Y ∈ L∞` and a
convex (hence continuous) `ℓ : ℝ → ℝ` the integrand is essentially bounded, so on a probability
space the integral is the true expectation. The convexity of `ℓ` and the position of `λ` are not
part of the definition; they are hypotheses of the theorems. -/
def acceptanceSet {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (ℓ : ℝ → ℝ) (lam : ℝ) :
    Set (Ω → ℝ) :=
  {Y | MemLp Y ⊤ μ ∧ ∫ ω, ℓ (-Y ω) ∂μ ≤ lam}

end OnlineUBSR


