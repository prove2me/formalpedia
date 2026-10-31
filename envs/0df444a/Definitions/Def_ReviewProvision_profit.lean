-- Prove2me | Definitions.Def_ReviewProvision_profit
-- name    : ReviewProvision_profit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:54:53.311048+00:00
-- url     : https://prove2.me/theorems/33914025-e8e8-433f-b07f-697eeb71e704
-- title:
--   The firm's profit $\Pi_\psi(\vec k)$
-- statement:
--   At sales $\vec k$ the first-period price of cluster $n$ is $p_{n1}=(1-k_n)/h$, and the firm's **profit** under policy $\psi$ is
--
--   $$
--   \Pi_\psi(\vec k)=\sum_{n=1}^N\frac{k_n(1-k_n)}{h}+\mathbb E\bigl[\Pi_2^*(v_{\psi1}(\vec k),\dots,v_{\psi N}(\vec k))\bigr],
--   $$
--
--   where $\Pi_2^*$ is the optimal second-period payoff.
--
--   **Formalization Note** The second term is an expectation under the prior of a function of conditional expectations, so all of the Bayesian content is in the profit. Its truncated Gaussian form (6) is the theorem `eq_6`. The decision variable is the sales vector, as in (6).
-- source:
--   Xiao, Chen, Tang, Customer Review Provision Policies with Heterogeneous Cluster Preferences, SSRN 3403322 (manuscript of 2021-05-24), (5)–(6), p.15

import Mathlib
import Definitions.Def_ReviewProvision_posteriorMean
import Definitions.Def_ReviewProvision_secondPeriodPayoff

open MeasureTheory ProbabilityTheory

namespace ReviewProvision

/-- The **first-period price** at sales `k`: `p_{n1} = (1 − k_n)/h`. SSRN 3403322 (manuscript of
2021-05-24), p.15 (PDF 15): "Because `k_n = q_p − h p_{n1}`, `n ∈ C`, and `q_p = 1`". -/
noncomputable def firstPeriodPrice {N : ℕ} (p : Params) (k : Fin N → ℝ) (n : Fin N) : ℝ :=
  (1 - k n) / p.h

/-- **The firm's profit** under a policy at sales `k`:
`Π_ψ(~k) = Σ_n k_n (1 − k_n)/h + E[Π*_2(v_{ψ1}(~k), …, v_{ψN}(~k))]`.
SSRN 3403322 (manuscript of 2021-05-24), (5)–(6), p.15 (PDF 15).

**Formalization Note.** The second term is the expectation under the prior of the optimal
second-period payoff of the conditional expectations `posteriorMean`, so the Bayesian model is the
content of the profit; the truncated-Gaussian integral of (6) is the theorem `eq_6`. The payoff is
integrable, since it is at most `Σ_n m v_{ψn}²/(4h)` and `v_{ψn}` is in `L²`, so no junk value of the
Bochner integral arises. The decision is the sales vector, as in (6). -/
noncomputable def profit {N : ℕ} (p : Params) (ψ : Policy) (k : Fin N → ℝ) : ℝ :=
  ∑ n, k n * (1 - k n) / p.h +
    ∫ ω, secondPeriodPayoff p (fun n => posteriorMean p k ψ n ω) ∂(prior p N)

end ReviewProvision


