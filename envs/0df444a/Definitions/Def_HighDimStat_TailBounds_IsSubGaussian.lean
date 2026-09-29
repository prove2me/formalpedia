-- Prove2me | Definitions.Def_HighDimStat_TailBounds_IsSubGaussian
-- name    : HighDimStat_TailBounds_IsSubGaussian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:18:54.596861+00:00
-- url     : https://prove2.me/theorems/24dead3f-a10c-4aea-8089-57f3692b9666
-- title:
--   A sub-Gaussian random variable with parameter sigma
-- statement:
--   **Definition 2.2.** A random variable $X$ with mean $\mu=\mathbb E[X]$ is **sub-Gaussian**
--   with parameter $\sigma$ if
--
--   $$
--   \mathbb E[e^{\lambda(X-\mu)}] \;\le\; e^{\sigma^2\lambda^2/2} \qquad \text{for all } \lambda \in \mathbb R.
--   $$
--
--   Any Gaussian variable with variance $\sigma^2$ is sub-Gaussian with parameter $\sigma$; this
--   condition is what Theorem 2.26's conclusion asserts about $f(X)-\mathbb E[f(X)]$.
--
--   **Formalization Note** Integrability of $X$ and of every exponential moment
--   $\mathbb E[e^{\lambda(X-\mu)}]$ is required as an explicit conjunct, guarding against
--   Mathlib's Bochner integral silently evaluating to $0$ on a non-integrable function.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 23 (PDF p. 43), Definition 2.2, Eq. (2.8)

import Mathlib

open MeasureTheory

namespace HighDimStat.TailBounds

/-- **Definition 2.2**, Wainwright, *High-Dimensional Statistics* (2019), p. 23. A random
variable `X` with mean `μ = E[X]` is sub-Gaussian with parameter `σ` if
`E[e^{λ(X-μ)}] ≤ e^{σ²λ²/2}` for all `λ ∈ ℝ`. Integrability of `X` and of every exponential
moment is required explicitly so that neither condition trivializes via the Bochner integral's
junk value on a non-integrable function. -/
def IsSubGaussian {Ω : Type*} [MeasurableSpace Ω] (X : Ω → ℝ) (Prob : Measure Ω) (sigma : ℝ) :
    Prop :=
  Integrable X Prob ∧
  (∀ lam : ℝ, Integrable (fun ω => Real.exp (lam * (X ω - ∫ ω', X ω' ∂Prob))) Prob) ∧
  (∀ lam : ℝ, ∫ ω, Real.exp (lam * (X ω - ∫ ω', X ω' ∂Prob)) ∂Prob ≤
    Real.exp (sigma ^ 2 * lam ^ 2 / 2))

end HighDimStat.TailBounds


