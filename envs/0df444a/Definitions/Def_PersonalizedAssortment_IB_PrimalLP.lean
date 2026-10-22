-- Prove2me | Definitions.Def_PersonalizedAssortment_IB_PrimalLP
-- name    : PersonalizedAssortment_IB_PrimalLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T01:44:26.398467+00:00
-- url     : https://prove2.me/theorems/c9f1b7af-7af6-4878-8fbc-ca5e56b13c3a
-- title:
--   The benchmark LP $\mathrm{Primal}(\{z_t\})$ and its dual
-- statement:
--   Fix products with revenues $r_i$ and initial inventories $c_i$, a family $\mathcal S$ of feasible assortments, and a sequence of customer types $z_1,\dots,z_T$. The benchmark linear program $\mathrm{Primal}(\{z_t\}_{t=1}^T)$ has one variable $y^t(S)$ for each period $t$ and each $S\in\mathcal S$:
--   $$\begin{aligned}\text{maximize}\quad &\sum_{t=1}^T\sum_{S\in\mathcal S}\sum_{i=1}^n r_i\,\varphi_i^{z_t}(S)\,y^t(S)\\ \text{subject to}\quad &\sum_{t=1}^T\sum_{S\in\mathcal S}\varphi_i^{z_t}(S)\,y^t(S)\le c_i\quad(1\le i\le n),\\ &\sum_{S\in\mathcal S}y^t(S)=1\quad(1\le t\le T),\qquad y^t(S)\ge0 .\end{aligned}$$
--   The variable $y^t(S)$ is the probability that a clairvoyant seller offers $S$ in period $t$. Its dual $\mathrm{Dual}(\{z_t\}_{t=1}^T)$ has variables $\lambda^t$ and $\theta_i$:
--   $$\begin{aligned}\text{minimize}\quad &\sum_{t=1}^T\lambda^t+\sum_{i=1}^n\theta_i c_i\\ \text{subject to}\quad &\lambda^t\ge\sum_{i=1}^n\varphi_i^{z_t}(S)(r_i-\theta_i)\quad(1\le t\le T,\ S\in\mathcal S),\qquad \theta_i\ge0 .\end{aligned}$$
--   This item defines primal feasibility, the primal objective, dual feasibility and the dual objective.
--
--   By Lemma 1 of the paper, the optimal value of the primal upper-bounds the expected revenue of every online algorithm. The competitive ratio is measured against it.
--
--   **Formalization Note** Periods are indexed by $\{0,\dots,T-1\}$, so the paper's period $t$ is index $t-1$. The LP optimum is never used. Every statement quantifies over feasible primal solutions $y$ instead, so no attainment or boundedness question arises.
-- source:
--   Golrezaei, Nazerzadeh, Rusmevichientong, Real-Time Optimization of Personalized Assortments, Management Sci. 60(6), 2014, https://doi.org/10.1287/mnsc.2014.1939, p. 1536, Lemma 1 (Primal); p. 1548, Section A.3 (Dual)

import Mathlib
import Definitions.Def_PersonalizedAssortment_IB_ChoiceModel

namespace PersonalizedAssortment.IB

variable {n : ℕ} {Z : Type*} {T : ℕ}

/-- Feasibility for the linear program `Primal({z_t}_{t=1}^T)` of Lemma 1, p. 1536. Periods are
indexed by `Fin T` (period `t` of the paper is `t - 1` here); `y t S = y^t(S)` for `S ∈ 𝒮`:
* `y^t(S) ≥ 0` for every period and every `S ∈ 𝒮`;
* `∑_{S ∈ 𝒮} y^t(S) = 1` for every period;
* `∑_t ∑_{S ∈ 𝒮} φ_i^{z_t}(S) y^t(S) ≤ c_i` for every product `i`. -/
def PrimalFeasible (c : Fin n → ℕ) (𝒮 : Finset (Finset (Fin n))) (φ : Z → ChoiceModel n)
    (z : Fin T → Z) (y : Fin T → Finset (Fin n) → ℝ) : Prop :=
  (∀ t : Fin T, ∀ S ∈ 𝒮, 0 ≤ y t S) ∧
  (∀ t : Fin T, ∑ S ∈ 𝒮, y t S = 1) ∧
  (∀ i : Fin n, ∑ t : Fin T, ∑ S ∈ 𝒮, (φ (z t)).prob S i * y t S ≤ (c i : ℝ))

/-- The objective of `Primal({z_t}_{t=1}^T)`:
`∑_{t=1}^T ∑_{S ∈ 𝒮} ∑_{i=1}^n r_i φ_i^{z_t}(S) y^t(S)`. -/
def primalObj (r : Fin n → ℝ) (𝒮 : Finset (Finset (Fin n))) (φ : Z → ChoiceModel n)
    (z : Fin T → Z) (y : Fin T → Finset (Fin n) → ℝ) : ℝ :=
  ∑ t : Fin T, ∑ S ∈ 𝒮, ∑ i : Fin n, r i * (φ (z t)).prob S i * y t S

/-- Feasibility for `Dual({z_t}_{t=1}^T)` (§A.3, p. 1548):
`λ^t ≥ ∑_{i=1}^n φ_i^{z_t}(S) (r_i - θ_i)` for every period `t` and every `S ∈ 𝒮`, and
`θ_i ≥ 0` for every product `i`. -/
def DualFeasible (r : Fin n → ℝ) (𝒮 : Finset (Finset (Fin n))) (φ : Z → ChoiceModel n)
    (z : Fin T → Z) (lam : Fin T → ℝ) (θ : Fin n → ℝ) : Prop :=
  (∀ t : Fin T, ∀ S ∈ 𝒮, ∑ i : Fin n, (φ (z t)).prob S i * (r i - θ i) ≤ lam t) ∧
  (∀ i : Fin n, 0 ≤ θ i)

/-- The objective of `Dual({z_t}_{t=1}^T)`: `∑_{t=1}^T λ^t + ∑_{i=1}^n θ_i c_i`. -/
def dualObj (c : Fin n → ℕ) (lam : Fin T → ℝ) (θ : Fin n → ℝ) : ℝ :=
  ∑ t : Fin T, lam t + ∑ i : Fin n, θ i * (c i : ℝ)

end PersonalizedAssortment.IB


