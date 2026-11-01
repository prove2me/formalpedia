-- Prove2me | Definitions.Def_WassChanceCvx_CVaR
-- name    : WassChanceCvx_CVaR
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T08:24:59.999182+00:00
-- url     : https://prove2.me/theorems/c031e49f-4dbd-4e6b-b08f-d1ee3ffe36e4
-- title:
--   Conditional value-at-risk $\mathrm{CVaR}_\beta$ (Definition 5)
-- statement:
--   For a probability distribution $\mu$ on $\mathbb R$ and a level $\beta<1$,
--
--   $$
--   \mathrm{CVaR}_\beta(\mu)=\inf_{\gamma\in\mathbb R}\Bigl\{\gamma+\frac1{1-\beta}\int(x-\gamma)^+\,d\mu(x)\Bigr\}.
--   $$
--
--   With $\beta=1-\epsilon$ the factor is $1/\epsilon$, so $\mathrm{CVaR}_{1-\epsilon}(\mathbb P_X)=\min_\gamma\{\gamma+\frac1\epsilon\mathbb E[(X-\gamma)^+]\}$, the paper's conditional value-at-risk of a random variable $X$ with law $\mathbb P_X$.
--
--   **Formalization Note** The paper's minimum is written as a real infimum; when $\mathbb E[X^+]<\infty$, $\mu$ is a probability measure and $\epsilon\in(0,1)$, the objective is finite and bounded below and the infimum is attained. The expectation is a Bochner integral, which Lean sets to $0$ for a non-integrable integrand; every statement using CVaR assumes $\mathbb E[X^+]<\infty$ or applies it to a variable bounded above.
-- source:
--   Shen, Jiang, Convex Chance-Constrained Programs with Wasserstein Ambiguity, arXiv:2111.02486v2, Definition 5, p.6

import Mathlib

open MeasureTheory

namespace WassChanceCvx

/-- **Conditional value-at-risk.**
Shen, Jiang, arXiv:2111.02486v2, Definition 5, p.6: "its `(1 − ϵ)`-CVaR is defined through
`CVaR_{1−ϵ}(X) := min_γ {γ + (1/ϵ) 𝔼[(X − γ)⁺]}`."

`CVaR β μ = inf_{γ ∈ ℝ} {γ + (1/(1 − β)) ∫ (x − γ)⁺ dμ(x)}` for a law `μ` on `ℝ`; with
`β = 1 − ϵ` the factor `1/(1 − β)` is `1/ϵ`, so `CVaR (1 - ϵ) (law of X)` is `CVaR_{1−ϵ}(X)`.

**Formalization Note.** The minimum is written as the real infimum `⨅ γ`. When `𝔼[X⁺] < ∞` and
`μ` is a probability measure with `β ∈ (0, 1)`, the objective is finite, bounded below and its
infimum is attained, so this is the paper's minimum. The expectation is a Bochner integral, which
is `0` for a non-integrable integrand; every statement that uses `CVaR` assumes `𝔼[X⁺] < ∞` or
applies it to a variable bounded above. -/
noncomputable def CVaR (β : ℝ) (μ : Measure ℝ) : ℝ :=
  ⨅ γ : ℝ, γ + (1 / (1 - β)) * ∫ x, max (x - γ) 0 ∂μ

end WassChanceCvx


