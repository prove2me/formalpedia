-- Prove2me | Definitions.Def_DRCVRP_RCI_DemandEstimator
-- name    : DRCVRP_RCI_DemandEstimator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:19:18.787432+00:00
-- url     : https://prove2.me/theorems/0690fa8b-8b02-41ef-ac0b-c7b1a7477532
-- title:
--   Worst-case value-at-risk and the demand estimator $d_{\mathcal P}$ of Eq. (2)
-- statement:
--   Let $\tilde{\boldsymbol q}\in\mathbb R^n$ be the random vector of customer demands and let $\mathcal P$ be an **ambiguity set**, a set of probability distributions of $\tilde{\boldsymbol q}$. Fix a risk level $\epsilon\in(0,1)$ and a vehicle capacity $Q>0$. For a random variable $\tilde X$ with distribution $\mathbb Q$, the value-at-risk is
--   $\mathbb Q\text{-VaR}_{1-\epsilon}[\tilde X]=\inf\{x\in\mathbb R:\ \mathbb Q[\tilde X\le x]\ge 1-\epsilon\}$.
--
--   For a customer set $S\subseteq V_C$, the **worst-case value-at-risk** of its cumulative demand is
--   $$
--   \sup_{\mathbb P\in\mathcal P}\ \mathbb P\text{-VaR}_{1-\epsilon}\Big[\sum_{i\in S}\tilde q_i\Big],
--   $$
--   and the **demand estimator** of Eq. (2) is
--   $$
--   d_{\mathcal P}(S)=\max\left\{\left\lceil\frac1Q\sup_{\mathbb P\in\mathcal P}\mathbb P\text{-VaR}_{1-\epsilon}\Big[\sum_{i\in S}\tilde q_i\Big]\right\rceil,\ 1\right\}\quad (S\neq\emptyset),\qquad d_{\mathcal P}(\emptyset)=0 .
--   $$
--   It is a lower bound on the number of vehicles needed to serve $S$. The estimator satisfies the **subadditivity condition (S)** if
--   $$
--   d_{\mathcal P}(S\cup T)\le d_{\mathcal P}(S)+d_{\mathcal P}(T)\qquad\text{for all customer subsets } S,T\subseteq V_C .
--   $$
--
--   The estimator is the right-hand side of the rounded capacity inequalities of 2VF($\mathcal P$); condition (S) is the hypothesis of Theorem 1.
--
--   **Formalization Note** Value-at-risk is the published `MultistageStochastic.valueAtRisk P X (1 - ε)`. The ambiguity set is `Amb : Set (Measure (Fin n → ℝ))` (the paper's $\mathcal P$). The supremum is Lean's real `sSup`, which returns $0$ on an empty or unbounded set: every theorem of the mission therefore assumes the image of the VaR map is bounded above (the paper's $d_{\mathcal P}$ is real valued). On an empty ambiguity set `sSup ∅ = 0` gives $d_{\mathcal P}(S)=1$ for $S\ne\emptyset$, which agrees with the paper's $\max\{\lceil-\infty\rceil,1\}=1$. $d_{\mathcal P}$ is integer valued.
-- source:
--   Ghosal and Wiesemann, The Distributionally Robust Chance-Constrained Vehicle Routing Problem, Oper. Res. 68(3) (2020) 716–732, §3, p. 720 (VaR), p. 721, Eq. (2), p. 722, condition (S)

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional

open MeasureTheory

namespace DRCVRP.RCI

/-- The worst-case value-at-risk `sup_{ℙ ∈ 𝒫} ℙ-VaR_{1-ε}[∑_{i ∈ S} q̃_i]` of the cumulative demand
of a customer set `S` over an ambiguity set `Amb` (the paper's `𝒫`) of distributions of the demand vector
`q̃ ∈ ℝⁿ` (§3, pp. 720–721). A real supremum; the theorems of the mission assume the image is
bounded above (the paper's `d_𝒫` is real valued). -/
noncomputable def worstCaseVaR {n : ℕ} (Amb : Set (Measure (Fin n → ℝ))) (ε : ℝ)
    (S : Finset (Fin n)) : ℝ :=
  sSup ((fun P => MultistageStochastic.valueAtRisk P (fun q => ∑ i ∈ S, q i) (1 - ε)) '' Amb)

/-- The demand estimator (2) (p. 721):
`d_𝒫(S) = max {⌈(1/Q) sup_{ℙ ∈ 𝒫} ℙ-VaR_{1-ε}[∑_{i ∈ S} q̃_i]⌉, 1}` for `S ≠ ∅`, and
`d_𝒫(∅) = 0`. -/
noncomputable def demandEstimator {n : ℕ} (Amb : Set (Measure (Fin n → ℝ))) (ε Q : ℝ)
    (S : Finset (Fin n)) : ℤ :=
  if S = ∅ then 0 else max ⌈worstCaseVaR Amb ε S / Q⌉ 1

/-- The subadditivity condition (S) (p. 722): `d_𝒫(S ∪ T) ≤ d_𝒫(S) + d_𝒫(T)` for all customer
subsets `S, T ⊆ V_C`. -/
def IsSubadditive {n : ℕ} (Amb : Set (Measure (Fin n → ℝ))) (ε Q : ℝ) : Prop :=
  ∀ S T : Finset (Fin n),
    demandEstimator Amb ε Q (S ∪ T) ≤ demandEstimator Amb ε Q S + demandEstimator Amb ε Q T

end DRCVRP.RCI


