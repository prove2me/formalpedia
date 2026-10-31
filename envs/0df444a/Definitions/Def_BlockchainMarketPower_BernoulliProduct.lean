-- Prove2me | Definitions.Def_BlockchainMarketPower_BernoulliProduct
-- name    : BlockchainMarketPower_BernoulliProduct
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:25:17.445212+00:00
-- url     : https://prove2.me/theorems/55a74e52-4df9-4ce4-97d2-9a62aa2f5f8a
-- title:
--   Independent Bernoulli coordinates: weight, expectation, variance, mean-variance utility
-- statement:
--   Fix $N\in\mathbb N$ and $\theta\in\mathbb R$. On the finite sample space $\{\text{true},\text{false}\}^N$ of outcomes $b=(b_1,\dots,b_N)$, the product law with independent coordinates, each true with probability $\theta$, gives the outcome $b$ the weight
--
--   $$
--   w_\theta(b)=\prod_{j=1}^N\bigl(\theta\ \text{ if } b_j,\ \text{ otherwise } 1-\theta\bigr).
--   $$
--
--   For a function $X$ on the sample space,
--
--   $$
--   \mathbb E_\theta[X]=\sum_b w_\theta(b)\,X(b),\qquad \mathrm{Var}_\theta[X]=\mathbb E_\theta[X^2]-\mathbb E_\theta[X]^2,
--   $$
--
--   and, for $\gamma\in\mathbb R$, the mean-variance utility of $X$ is $\mathbb E_\theta[X]-\frac{\gamma}{2}\mathrm{Var}_\theta[X]$.
--
--   This finite probability space carries the batch outcomes of the supply chain model, and the mean-variance utility is the manufacturer's objective.
--
--   **Formalization Note** For $\theta\in[0,1]$ the weights form a probability vector. Outside that range the formulas are still defined; the model only uses $\theta=\sqrt e$ with $e\in[0,1]$ wherever the value matters.
-- source:
--   Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, the batch indicators of (11), p.17, (10), p.16, and the variance on p.38

import Mathlib

namespace BlockchainMarketPower

/-- The product law on `Fin N → Bool` with independent coordinates, each `true` with probability
`θ`: the weight of the outcome `b` is `∏ⱼ (θ if b j, else 1 - θ)`.
Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, the batch indicators of (11), p.17, and the variance
on p.38.

**Formalization Note.** The paper never says that defects are independent across suppliers;
(2) multiplies the survival probabilities and the factor `1/|Ξ|` on p.38 requires it. For
`θ ∈ [0, 1]` this is a probability vector; elsewhere it is only a formula, and the callers feed it
`θ = √e` with `e ∈ [0, 1]`. -/
noncomputable def bernoulliWeight {N : ℕ} (θ : ℝ) (b : Fin N → Bool) : ℝ :=
  ∏ j, if b j then θ else 1 - θ

/-- Expectation of `X` under `bernoulliWeight θ`, a finite weighted sum. -/
noncomputable def bernoulliExpect {N : ℕ} (θ : ℝ) (X : (Fin N → Bool) → ℝ) : ℝ :=
  ∑ b, bernoulliWeight θ b * X b

/-- Variance of `X` under `bernoulliWeight θ`: `E[X²] - E[X]²`. -/
noncomputable def bernoulliVar {N : ℕ} (θ : ℝ) (X : (Fin N → Bool) → ℝ) : ℝ :=
  bernoulliExpect θ (fun b => X b ^ 2) - bernoulliExpect θ X ^ 2

/-- The mean-variance utility `E[X] - (γ/2) Var[X]` under `bernoulliWeight θ`.
Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, (10), p.16. -/
noncomputable def meanVariance {N : ℕ} (γ θ : ℝ) (X : (Fin N → Bool) → ℝ) : ℝ :=
  bernoulliExpect θ X - γ / 2 * bernoulliVar θ X

end BlockchainMarketPower


