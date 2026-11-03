-- Prove2me | Definitions.Def_RegimeDRCVaR_Scenario
-- name    : RegimeDRCVaR_Scenario
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:22:38.763089+00:00
-- url     : https://prove2.me/theorems/26fbcc3e-7ccb-4545-8218-abd5e5677d5d
-- title:
--   Sample space $\mathbb R^I\times\mathbb R^K\times([K]\times\mathbb N)$ of $(\tilde r,\tilde u,\tilde k,\tilde n)$
-- statement:
--   An outcome of the regime-switching ambiguity set is a quadruple $(\tilde r,\tilde u,\tilde n,\tilde k)$: a return vector $\tilde r\in\mathbb R^I$, a vector of auxiliary variables $\tilde u=(\tilde u_1,\dots,\tilde u_K)'\in\mathbb R^K$, a regime $\tilde k\in[K]$ and a scenario $\tilde n$ of that regime.
--
--   The sample space carries the product of the Borel $\sigma$-algebras of $\mathbb R^I$ and $\mathbb R^K$ and the discrete $\sigma$-algebras of the two indices.
--
--   **Formalization Note** The paper's space is $\mathbb R^I\times\mathbb R^K\times[N_k]_{k=1}^K\times[K]$. Here an outcome is `(r̃, ũ, (k̃, ñ))` with `k̃ : Fin K` (regime $k$ is the index $k-1$) and `ñ : ℕ` (scenario $n$ is the index $n-1$); the laws of the ambiguity set put all of their mass on $\tilde n<N_{\tilde k}$.
-- source:
--   Pun, Wang, Yan, Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set, SSRN 4378930, display (9), p.11

import Mathlib

namespace RegimeDRCVaR

/-- **The sample space of the regime-switching ambiguity set**
(Pun, Wang, Yan, *Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set*, SSRN 4378930, display (9), p.11): an outcome is
`(r̃, ũ, (k̃, ñ))` with return `r̃ ∈ ℝ^I`, auxiliary vector `ũ ∈ ℝ^K`, regime `k̃ ∈ [K]` and
scenario `ñ`.

**Formalization Note** The paper's space is `ℝ^I × ℝ^K × [N_k]_{k=1}^K × [K]`. Here the regime is
`Fin K` (regime `k` of the paper is the index `k − 1`) and the scenario is a natural number; the
laws in `Urs` put all the mass on the pairs `(k, n)` with `n < N_k` (scenario `n + 1` of the
paper). The σ-algebra is the product of the Borel σ-algebras of `ℝ^I`, `ℝ^K` and the discrete
σ-algebras of `Fin K` and `ℕ`. -/
abbrev Scenario (I K : ℕ) : Type := (Fin I → ℝ) × (Fin K → ℝ) × (Fin K × ℕ)

end RegimeDRCVaR


