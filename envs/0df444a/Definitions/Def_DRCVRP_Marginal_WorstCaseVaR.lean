-- Prove2me | Definitions.Def_DRCVRP_Marginal_WorstCaseVaR
-- name    : DRCVRP_Marginal_WorstCaseVaR
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:35:53.882023+00:00
-- url     : https://prove2.me/theorems/3af89ddd-2fd9-4552-90d1-f312c94defc9
-- title:
--   Worst-case value-at-risk $\sup_{\mathbb P\in\mathcal P}\mathbb P\text{-VaR}_{1-\epsilon}[\sum_{i\in S}\tilde q_i]$ over an ambiguity set
-- statement:
--   Consider $n$ customers $V_C=\{1,\dots,n\}$ with an uncertain demand vector $\tilde{\boldsymbol q}\in\mathbb R^n$. Its distribution is only known to belong to an **ambiguity set** $\mathcal P$ of probability distributions on $\mathbb R^n$. Fix a risk level $\epsilon\in(0,1)$.
--
--   For a distribution $\mathbb P$ and a real random variable $\tilde X$, the value-at-risk at level $1-\epsilon$ is
--   $$
--   \mathbb P\text{-VaR}_{1-\epsilon}[\tilde X]=\inf\{x\in\mathbb R:\ \mathbb P[\tilde X\le x]\ge 1-\epsilon\}.
--   $$
--   For a customer subset $S\subseteq V_C$, the **worst-case value-at-risk** of the cumulative demand of $S$ is
--   $$
--   \sup_{\mathbb P\in\mathcal P}\ \mathbb P\text{-VaR}_{1-\epsilon}\Big[\sum_{i\in S}\tilde q_i\Big].
--   $$
--   The single-customer worst-case value-at-risk $\sup_{\mathbb P\in\mathcal P}\mathbb P\text{-VaR}_{1-\epsilon}[\tilde q_i]$ is the case $S=\{i\}$.
--
--   The worst-case value-at-risk is the smallest capacity that a vehicle serving the customers in $S$ needs so that its capacity constraint holds with probability at least $1-\epsilon$ under every distribution in $\mathcal P$.
--
--   **Formalization Note** Customers are `Fin n` (0-based) and distributions are measures on `Fin n → ℝ`. The value-at-risk is the published `MultistageStochastic.valueAtRisk P Y (1 - ε)`, the infimum of $\{y:\ 1-\epsilon\le\mathbb P(Y\le y)\}$. The supremum is the real `sSup` of the image of the ambiguity set. A real `sSup` is $0$ on an empty or unbounded set; for the marginalized moment ambiguity sets of this mission under their standing assumptions the image is nonempty (the Dirac measure at $\boldsymbol\mu$ belongs to the set) and bounded (every value-at-risk lies between $\sum_{i\in S}\underline q_i$ and $\sum_{i\in S}\overline q_i$), so `sSup` is the true supremum. The single-customer value is written `worstCaseVaR 𝒫 ε {i}`.
-- source:
--   Ghosal and Wiesemann, The Distributionally Robust Chance-Constrained Vehicle Routing Problem, Oper. Res. 68(3) (2020) 716–732, §3, p. 720 (value-at-risk), p. 721, Eq. (2), p. 723, Theorem 3 (worst-case value-at-risk)

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional

open MeasureTheory

namespace DRCVRP.Marginal

/-!
Ghosal and Wiesemann, *The Distributionally Robust Chance-Constrained Vehicle Routing Problem*,
Oper. Res. 68(3) (2020). Customers are `Fin n` (the paper's `V_C = {1,…,n}`, 0-based); a demand
vector is `q : Fin n → ℝ`, and distributions of the random demand vector are measures on
`Fin n → ℝ`.
-/

/-- The worst-case value-at-risk `sup_{ℙ ∈ 𝒫} ℙ-VaR_{1-ε}[∑_{i ∈ S} q̃_i]` of the total demand of
the customer set `S` over the ambiguity set `Amb` (p. 721, Eq. (2); p. 723, Theorem 3), with
`ℙ-VaR_{1-ε}[X̃] = inf {x ∈ ℝ : ℙ[X̃ ≤ x] ≥ 1 - ε}` (p. 720). The supremum is the real `sSup`
of the image of `Amb`; the single-customer value `sup_{ℙ ∈ 𝒫} ℙ-VaR_{1-ε}[q̃_i]` is
`worstCaseVaR Amb ε {i}`. -/
noncomputable def worstCaseVaR {n : ℕ} (Amb : Set (Measure (Fin n → ℝ))) (ε : ℝ)
    (S : Finset (Fin n)) : ℝ :=
  sSup ((fun P => MultistageStochastic.valueAtRisk P (fun q => ∑ i ∈ S, q i) (1 - ε)) '' Amb)

end DRCVRP.Marginal


