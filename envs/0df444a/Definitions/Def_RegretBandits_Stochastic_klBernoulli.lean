-- Prove2me | Definitions.Def_RegretBandits_Stochastic_klBernoulli
-- name    : RegretBandits_Stochastic_klBernoulli
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T02:03:36.218289+00:00
-- url     : https://prove2.me/theorems/4587375c-b502-42c3-9e94-837006e12a41
-- title:
--   Bernoulli Kullback–Leibler divergence $\mathrm{kl}(p,q)$
-- statement:
--   For $p,q\in[0,1]$, $\mathrm{kl}(p,q)$ is the Kullback–Leibler divergence between a Bernoulli distribution of parameter $p$ and one of parameter $q$:
--   $$\mathrm{kl}(p,q)=p\ln\frac pq+(1-p)\ln\frac{1-p}{1-q},$$
--   with $0\ln(\cdot)=0$.
--
--   It is the quantity in the constant of the distribution-dependent lower bound (Theorem 2.2) and in the comparison (2.8).
--
--   **Formalization Note.** The formula is real-valued. It gives the book's value for every $p\in[0,1]$ and $q\in(0,1)$. At $q\in\{0,1\}$ with $p\neq q$ the true value is $+\infty$ and the real formula returns a junk number, so every statement using it excludes that case explicitly.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 12, Section 2.3

import Mathlib

namespace RegretBandits.Stochastic

/-- `kl(p, q) = p ln(p/q) + (1 - p) ln((1 - p)/(1 - q))`, the Kullback–Leibler divergence between
Bernoulli distributions of parameters `p` and `q` (Bubeck and Cesa-Bianchi, arXiv:1204.5721v2,
p. 12). With Lean's conventions `0 * x = 0`, the formula gives the book's values for every
`p ∈ [0, 1]` and `q ∈ (0, 1)`; at `q ∈ {0, 1}`, `p ≠ q`, the book's value is `+∞` and this real
formula returns a junk value, so every statement using it excludes that case. -/
noncomputable def klBern (p q : ℝ) : ℝ :=
  p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))

end RegretBandits.Stochastic


