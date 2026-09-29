-- Prove2me | Definitions.Def_HighDimStat_MetricEntropy_SubGaussianProcess
-- name    : HighDimStat_MetricEntropy_SubGaussianProcess
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:32:14.500841+00:00
-- url     : https://prove2.me/theorems/6d246959-ba6b-472e-9c14-8fb2ced279df
-- title:
--   A zero-mean sub-Gaussian process with respect to a pseudometric
-- statement:
--   **Definition 5.16.** A collection of zero-mean random variables $\{X_\theta, \theta \in T\}$
--   is a **sub-Gaussian process** with respect to a (pseudo)metric $\rho_X$ on $T$ if
--
--   $$
--   \mathbb E\big[e^{\lambda(X_\theta - X_{\theta'})}\big] \;\le\; e^{\lambda^2 \rho_X(\theta,\theta')^2/2}
--   \qquad \text{for all } \theta,\theta' \in T,\ \lambda \in \mathbb R.
--   $$
--
--   This generalizes the canonical Gaussian process and the Rademacher process, and is the
--   object every result of Chapter 5's chaining section (5.3) is stated about.
--
--   **Formalization Note** $\rho_X$ is realized as `dist` from a `PseudoMetricSpace T` instance
--   given on the index type $T$. Integrability of each $X_\theta$ and of the exponential moments
--   $\mathbb E[e^{\lambda(X_\theta-X_{\theta'})}]$ is required as an explicit conjunct: without it,
--   Mathlib's Bochner integral silently evaluates to $0$ on a non-integrable function, which would
--   let both the zero-mean condition and the MGF bound hold vacuously regardless of the process's
--   actual behavior.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 134 (PDF p. 154), Definition 5.16, Eq. (5.32)

import Mathlib

open MeasureTheory

namespace HighDimStat.MetricEntropy

/-- **Definition 5.16**, Wainwright, *High-Dimensional Statistics* (2019), p. 134. A collection of
zero-mean random variables `{Xθ, θ ∈ T}` is a sub-Gaussian process with respect to a (pseudo)metric
`ρX` on `T` (realized here as `dist` from a `PseudoMetricSpace T` instance) if
`E[e^{λ(Xθ-Xθ')}] ≤ e^{λ²ρX(θ,θ')²/2}` for all `θ, θ' ∈ T` and `λ ∈ ℝ` (Eq. (5.32)). Integrability
of each `Xθ` and of the exponential moments is required so that neither the mean-zero condition
nor the MGF bound trivializes via the Bochner integral's junk value on non-integrable functions. -/
def SubGaussianProcess {T Ω : Type*} [PseudoMetricSpace T] [MeasurableSpace Ω]
    (Prob : Measure Ω) (X : T → Ω → ℝ) : Prop :=
  (∀ θ : T, Integrable (X θ) Prob) ∧
  (∀ θ : T, ∫ ω, X θ ω ∂Prob = 0) ∧
  (∀ θ θ' : T, ∀ lam : ℝ, Integrable (fun ω => Real.exp (lam * (X θ ω - X θ' ω))) Prob) ∧
  (∀ θ θ' : T, ∀ lam : ℝ,
    ∫ ω, Real.exp (lam * (X θ ω - X θ' ω)) ∂Prob ≤ Real.exp (lam ^ 2 * dist θ θ' ^ 2 / 2))

end HighDimStat.MetricEntropy


