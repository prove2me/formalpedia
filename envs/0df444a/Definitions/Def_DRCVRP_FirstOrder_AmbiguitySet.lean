-- Prove2me | Definitions.Def_DRCVRP_FirstOrder_AmbiguitySet
-- name    : DRCVRP_FirstOrder_AmbiguitySet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:47:10.067359+00:00
-- url     : https://prove2.me/theorems/24420a2d-dc93-4b7c-b509-ae3c339e0940
-- title:
--   First-order generic moment ambiguity set and worst-case value-at-risk
-- statement:
--   Let $V_C=\{1,\dots,n\}$ be the customers of a vehicle routing problem and let the random demand vector $\tilde{\boldsymbol q}$ take values in $\mathbb R^n$. Fix a box $\mathcal Q=[\underline{\boldsymbol q},\overline{\boldsymbol q}]$, a mean vector $\boldsymbol\mu$, customer subsets $S_1,\dots,S_p\subseteq V_C$ and dispersion bounds $\boldsymbol\nu\in\mathbb R^p$. The **first-order generic moment ambiguity set** is
--
--   $$
--   \mathcal P=\Bigl\{\mathbb P\in\mathcal P_0(\mathbb R^n)\;:\;\mathbb P[\tilde{\boldsymbol q}\in\mathcal Q]=1,\ \ \mathbb E_{\mathbb P}[\tilde{\boldsymbol q}]=\boldsymbol\mu,\ \ \mathbb E_{\mathbb P}\Bigl[\textstyle\sum_{j\in S_i}|\tilde q_j-\mu_j|\Bigr]\le\nu_i\ \ \forall i=1,\dots,p\Bigr\},
--   $$
--
--   where $\mathcal P_0(\mathbb R^n)$ is the set of probability distributions on $\mathbb R^n$. It bounds the mean absolute deviation of the cumulative demand of each prescribed customer subset.
--
--   For a customer subset $S\subseteq V_C$ and a risk level $\epsilon$, the **worst-case value-at-risk** of the cumulative demand of $S$ over a set $\mathcal P$ of distributions is
--
--   $$
--   \sup_{\mathbb P\in\mathcal P}\ \mathbb P\text{-VaR}_{1-\epsilon}\Bigl[\textstyle\sum_{i\in S}\tilde q_i\Bigr],\qquad \mathbb P\text{-VaR}_{1-\epsilon}[\tilde X]=\inf\{x\in\mathbb R:\mathbb P[\tilde X\le x]\ge1-\epsilon\}.
--   $$
--
--   These are the objects of Theorem 5 and Corollaries 2 and 3 of the paper: a route serving the customers $S$ satisfies the distributionally robust capacity constraint exactly when this worst-case value-at-risk does not exceed the vehicle capacity.
--
--   **Formalization Note** Customers are indexed $0,\dots,n-1$ (`Fin n`), a distribution is a measure on `Fin n → ℝ` that is required to be a probability measure, and the subsets are a family `Sfam : Fin p → Finset (Fin n)`. The expectations are Bochner integrals with explicit integrability clauses; for a probability measure carried by the box these clauses hold automatically, so they do not change the set. The value-at-risk is the published `MultistageStochastic.valueAtRisk` at level $1-\epsilon$, and the supremum is the real `sSup` of the image of the set; under the paper's assumptions that image is nonempty (it contains the Dirac distribution at $\boldsymbol\mu$) and bounded (the support is the box), so the real supremum is the paper's.
-- source:
--   Ghosal and Wiesemann, The Distributionally Robust Chance-Constrained Vehicle Routing Problem, Oper. Res. 68(3) (2020) 716–732, https://doi.org/10.1287/opre.2019.1924, §5.1, p. 725, Eq. (12); §3, p. 721 (worst-case VaR in Eq. (2)); §3, p. 720 (definition of VaR)

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional

open MeasureTheory

namespace DRCVRP.FirstOrder

/-!
Ghosal and Wiesemann, *The Distributionally Robust Chance-Constrained Vehicle Routing Problem*,
Oper. Res. 68(3) (2020), §5.1, p. 725. Customers are `Fin n` (the paper's `V_C = {1,…,n}`,
0-based); a demand vector is `q : Fin n → ℝ`, and distributions of the random demand vector
`q̃` are measures on `Fin n → ℝ`. The customer subsets `S_1, …, S_p` are `Sfam : Fin p → Finset
(Fin n)` (0-based).
-/

/-- The first-order generic moment ambiguity set (12) (§5.1, p. 725):
`𝒫 = {ℙ ∈ 𝒫₀(ℝⁿ) : ℙ[q̃ ∈ 𝒬] = 1, 𝔼_ℙ[q̃] = μ, 𝔼_ℙ[1_{S_l}ᵀ |q̃ − μ|] ≤ ν_l ∀ l}` with the
rectangular support `𝒬 = [qlo, qhi]`, the mean vector `μ`, the customer subsets `Sfam l` and the
mean-absolute-deviation bounds `ν l`; `1_{S_l}ᵀ |q̃ − μ| = ∑_{j ∈ S_l} |q̃_j − μ_j|`.
The integrability clauses make the expectations genuine Bochner integrals; for a probability
measure carried by the box they hold automatically, so they do not shrink the set. -/
def firstOrderAmbiguitySet {n p : ℕ} (qlo qhi μ : Fin n → ℝ) (Sfam : Fin p → Finset (Fin n))
    (ν : Fin p → ℝ) : Set (Measure (Fin n → ℝ)) :=
  {P | IsProbabilityMeasure P ∧ P (Set.Icc qlo qhi) = 1 ∧
    (∀ j, Integrable (fun q => q j) P ∧ ∫ q, q j ∂P = μ j) ∧
    ∀ l, Integrable (fun q => ∑ j ∈ Sfam l, |q j - μ j|) P ∧
      ∫ q, (∑ j ∈ Sfam l, |q j - μ j|) ∂P ≤ ν l}

/-- The worst-case value-at-risk `sup_{ℙ ∈ 𝒫} ℙ-VaR_{1-ε}[∑_{i ∈ S} q̃_i]` of the cumulative
demand of the customer subset `S` over an ambiguity set `Amb` (the paper's `𝒫`) (§3, p. 721;
§5.1, p. 726, Theorem 5), with `ℙ-VaR_{1-ε}[X̃] = inf {x ∈ ℝ : ℙ[X̃ ≤ x] ≥ 1 - ε}` (p. 720).
The supremum is the real `sSup` of the image of `Amb`. -/
noncomputable def worstCaseVaR {n : ℕ} (Amb : Set (Measure (Fin n → ℝ))) (ε : ℝ)
    (S : Finset (Fin n)) : ℝ :=
  sSup ((fun P => MultistageStochastic.valueAtRisk P (fun q => ∑ i ∈ S, q i) (1 - ε)) '' Amb)

end DRCVRP.FirstOrder


