-- Prove2me | Definitions.Def_ConvBoundsQA_Lam
-- name    : ConvBoundsQA_Lam
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:26:15.56157+00:00
-- url     : https://prove2.me/theorems/f2c17619-f89a-4805-8c88-fb7e18ade5da
-- title:
--   Couplings $\Gamma(\mu)$ and aggregate laws $\Lambda(\mu)$
-- statement:
--   For $\mu=(\mu_1,\dots,\mu_n)\in\mathcal M^n$, let $\Gamma(\mu)$ be the set of probability measures on $\mathbb R^n$ with one-dimensional marginals $\mu_1,\dots,\mu_n$. For a probability measure $\pi$ on $\mathbb R^n$, its **aggregate law** $\lambda_\pi\in\mathcal M$ is
--   $$
--   \lambda_\pi(-\infty,x]=\pi\{(x_1,\dots,x_n):x_1+\dots+x_n\le x\},\qquad x\in\mathbb R,
--   $$
--   the law of $X_1+\dots+X_n$ when $(X_1,\dots,X_n)\sim\pi$, and
--   $$
--   \Lambda(\mu)=\{\lambda_\pi:\pi\in\Gamma(\mu)\}
--   $$
--   is the set of distributions of the sum with the given marginals.
--
--   The worst-case quantile and RVaR of an aggregate risk under dependence uncertainty are suprema over $\Lambda(\mu)$.
--
--   **Formalization Note** $\mathbb R^n$ is `Fin n → ℝ`; every coupling is allowed (not only the product or comonotone ones). $\Gamma(\mu)$ always contains the product measure.
-- source:
--   Blanchet, Lam, Liu, Wang, Convolution Bounds on Quantile Aggregation, arXiv:2007.09320v5, §3, pp.6–7

import Mathlib

open MeasureTheory

namespace ConvBoundsQA

/-- The set `Γ(μ)` of probability measures on `ℝⁿ` with one-dimensional marginals `μ₁, …, μₙ`
(Blanchet, Lam, Liu, Wang, arXiv:2007.09320v5, §3, p.6).

**Formalization Note** `ℝⁿ` is `Fin n → ℝ`; the `i`-th marginal is the image of `π` under the
coordinate projection `x ↦ x i`. Every coupling is admitted (not only the product or the comonotone
one); no atomless probability space is needed. -/
def Gam {n : ℕ} (μ : Fin n → Measure ℝ) : Set (Measure (Fin n → ℝ)) :=
  {π | IsProbabilityMeasure π ∧ ∀ i, π.map (fun x => x i) = μ i}

/-- The aggregate law `λ_π`: `λ_π(−∞, x] = π{x₁ + ⋯ + xₙ ⩽ x}`, the law of `X₁ + ⋯ + Xₙ` when
`(X₁, …, Xₙ) ∼ π` (Blanchet, Lam, Liu, Wang, arXiv:2007.09320v5, §3, pp.6–7). -/
noncomputable def aggLaw {n : ℕ} (π : Measure (Fin n → ℝ)) : Measure ℝ :=
  π.map (fun x => ∑ i, x i)

/-- The set `Λ(μ) = {λ_π : π ∈ Γ(μ)}` of aggregate distribution measures with marginals `μ`
(Blanchet, Lam, Liu, Wang, arXiv:2007.09320v5, §3, p.7). -/
def Lam {n : ℕ} (μ : Fin n → Measure ℝ) : Set (Measure ℝ) :=
  aggLaw '' Gam μ

end ConvBoundsQA


