-- Prove2me | Definitions.Def_HighDimStat_TailBounds_IsSubExponential
-- name    : HighDimStat_TailBounds_IsSubExponential
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:19:25.583976+00:00
-- url     : https://prove2.me/theorems/c471a42f-5808-438f-b6c8-c887abf430ec
-- title:
--   A sub-exponential random variable with parameters nu, alpha
-- statement:
--   **Definition 2.7.** A random variable $X$ with mean $\mu=\mathbb E[X]$ is **sub-exponential**
--   with parameters $(\nu,\alpha)$ if
--
--   $$
--   \mathbb E[e^{\lambda(X-\mu)}] \;\le\; e^{\nu^2\lambda^2/2} \qquad \text{for all } |\lambda| < 1/\alpha,
--   $$
--
--   with the convention that $1/0$ is interpreted as $+\infty$ (so $\alpha=0$ recovers the
--   unrestricted sub-Gaussian case). This is the class of random variables Theorem 2.19's
--   martingale Bernstein bound concludes membership in.
--
--   **Formalization Note** The condition `|λ| < 1/α` is realized as the disjunction
--   `α = 0 ∨ |λ| < 1/α`: Lean's real division gives `1/0 = 0`, which would otherwise make the
--   condition vacuous at `α=0` (no `λ` satisfies `|λ|<0`) instead of unrestricted, exactly
--   backwards from the book's own stated `1/0=+∞` convention. Integrability of $X$ and of every
--   admissible exponential moment is required explicitly, guarding against the Bochner integral's
--   junk value on a non-integrable function.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 26 (PDF p. 46), Definition 2.7, Eq. (2.13)

import Mathlib

open MeasureTheory

namespace HighDimStat.TailBounds

/-- **Definition 2.7**, Wainwright, *High-Dimensional Statistics* (2019), p. 26. A random
variable `X` with mean `μ = E[X]` is sub-exponential with parameters `(ν, α)` (both
nonnegative) if `E[e^{λ(X-μ)}] ≤ e^{ν²λ²/2}` for all `|λ| < 1/α`, with the book's own
convention that `1/0` is interpreted as `+∞` (so `α = 0` recovers the unrestricted, sub-Gaussian
case). Realized as the disjunction `α = 0 ∨ |λ| < 1/α`, since Lean's real division gives
`1/0 = 0`, which would otherwise make the defining condition vacuous (never applicable) at
`α = 0` instead of unrestricted, exactly backwards from the book's stated convention.
Integrability of `X` and of every exponential moment on the allowed range of `λ` is required
explicitly to block the Bochner integral's junk value on a non-integrable function. -/
def IsSubExponential {Ω : Type*} [MeasurableSpace Ω] (X : Ω → ℝ) (Prob : Measure Ω)
    (nu alpha : ℝ) : Prop :=
  Integrable X Prob ∧
  (∀ lam : ℝ, (alpha = 0 ∨ |lam| < 1 / alpha) →
    Integrable (fun ω => Real.exp (lam * (X ω - ∫ ω', X ω' ∂Prob))) Prob) ∧
  (∀ lam : ℝ, (alpha = 0 ∨ |lam| < 1 / alpha) →
    ∫ ω, Real.exp (lam * (X ω - ∫ ω', X ω' ∂Prob)) ∂Prob ≤ Real.exp (nu ^ 2 * lam ^ 2 / 2))

end HighDimStat.TailBounds


