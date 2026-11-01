-- Prove2me | Definitions.Def_BiasVarianceMinimax_mseWeighted
-- name    : BiasVarianceMinimax_mseWeighted
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:31:01.007452+00:00
-- url     : https://prove2.me/theorems/2bb91d83-f576-4bdc-9fd1-91d49017f5fd
-- title:
--   $\mathrm{MSE}_1^{gen}$: the mean squared error of the weighted estimator
-- statement:
--   For real weights $w=(w_j)_{j=1,\dots,n}$, the general weighted estimator is
--
--   $$\hat\theta_n^{gen}=\sum_{j=1}^n w_j\,\hat\theta_j(\delta_j),\qquad \delta_j=\tilde d(j+n_0)^{-\alpha},$$
--
--   with independent runs, and $\mathrm{MSE}_1^{gen}(\hat\theta(\cdot),\tilde d,w)=\mathbb E(\hat\theta_n^{gen}-\theta)^2$. The weights can have any sign and need not sum to $1$.
--
--   **Formalization Note** The expectation is the integral of the squared error under the product of the laws at the run-dependent $\delta_j$, over `Fin n`.
-- source:
--   Lam, Zhang & Zhang, arXiv:1902.04673v1, (21), p.19; §5.1, p.19

import Mathlib
import Definitions.Def_BiasVarianceMinimax_SimulationOutput
import Definitions.Def_BiasVarianceMinimax_deltaGrid

open MeasureTheory

namespace BiasVarianceMinimax

/-- `MSE₁^gen(θ̂(·), d̃, w^(n))`: the mean squared error of `θ̂ₙ^gen = ∑ⱼ wⱼ θ̂ⱼ(δⱼ)` with
`δⱼ = d̃ (j + n₀)^(-α)`. Lam, Zhang & Zhang, arXiv:1902.04673v1, (21), p.19 and §5.1, p.19.

**Formalization Note.** The runs are independent, as coordinates under the product over `Fin n` of
the laws at the run-dependent `δⱼ`. The weights are arbitrary reals. The integrand is integrable
(`Integrable` is proved from `SimulationOutput.memLp` in the verification file), so this is the true
expectation of the squared error and not a formula; the bias-variance form is a theorem. -/
noncomputable def mseWeighted {q₁ q₂ : ℝ} (M : SimulationOutput q₁ q₂) (n₀ : ℕ) (dTilde : ℝ) (n : ℕ)
    (w : Fin n → ℝ) : ℝ :=
  ∫ x : Fin n → ℝ, (∑ j, w j * x j - M.θ) ^ 2
    ∂Measure.pi (fun j : Fin n => M.law (deltaGrid q₁ q₂ n₀ dTilde j))

end BiasVarianceMinimax


