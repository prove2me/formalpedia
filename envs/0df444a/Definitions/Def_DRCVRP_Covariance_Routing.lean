-- Prove2me | Definitions.Def_DRCVRP_Covariance_Routing
-- name    : DRCVRP_Covariance_Routing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T03:31:00.283564+00:00
-- url     : https://prove2.me/theorems/8e796b8e-e1b3-4bf3-a32b-d4c8d7b2f58d
-- title:
--   Route sets and feasibility in the distributionally robust and the deterministic CVRP
-- statement:
--   Customers are $V_C=\{1,\dots,n\}$ and the depot has $m$ vehicles $K=\{1,\dots,m\}$ of capacity $Q$.
--
--   1. **Route sets.** $\mathfrak P(V_C,m)$ is the set of ordered partitions $\boldsymbol R=(R_1,\dots,R_m)$ of $V_C$ into $m$ nonempty, mutually disjoint, collectively exhaustive routes, each route $R_k=(R_{k,1},\dots,R_{k,n_k})$ an ordered list of customers.
--   2. **Distributionally robust feasibility.** Given an ambiguity set $\mathcal P$ and a risk level $\epsilon$, a route set $\boldsymbol R\in\mathfrak P(V_C,m)$ is feasible in RVRP($\mathcal P$) if
--   $$
--   \mathbb P\Big[\sum_{i\in R_k}\tilde q_i\le Q\Big]\ge1-\epsilon\qquad\forall\,\mathbb P\in\mathcal P,\ \forall\,k\in K.
--   $$
--   3. **Deterministic feasibility.** Given a capacity $Q'$ and demands $\boldsymbol q\in\mathbb R^n$, a route set $\boldsymbol R\in\mathfrak P(V_C,m)$ is feasible if $\sum_{i\in R_k}q_i\le Q'$ for every $k\in K$.
--
--   Feasibility depends only on which customers each route visits, not on the order; costs play no role here. These notions are used to compare the feasible regions of the stochastic and the deterministic vehicle routing problems.
--
--   **Formalization Note** Customers are `Fin n` (0-based) and vehicles `Fin m`. A route set is `R : Fin m → List (Fin n)` with every route nonempty and the concatenation of the routes a permutation of `List.finRange n`. The probability of the capacity event is compared in `ℝ≥0∞` through `ENNReal.ofReal (1 - ε)`.
-- source:
--   Ghosal and Wiesemann, The Distributionally Robust Chance-Constrained Vehicle Routing Problem, Oper. Res. 68(3) (2020) 716–732, §2, pp. 718–719 (route sets 𝔓(V_C, m), capacity constraint R_k ∈ ℛ(q), RVRP(𝒫))

import Mathlib

open MeasureTheory

namespace DRCVRP.Covariance

/-!
The route-set layer of Ghosal and Wiesemann, *The Distributionally Robust Chance-Constrained
Vehicle Routing Problem*, Oper. Res. 68(3) (2020), §2, pp. 718–719, as far as feasibility is
concerned (costs are not needed). Customers are `Fin n` (0-based), vehicles `Fin m`.
-/

/-- `R ∈ 𝔓(V_C, m)` (p. 718): `R = (R_1, …, R_m)` is an ordered partition of the customers into
`m` nonempty ordered routes; every customer occurs exactly once across all routes. -/
def IsRouteSet {n m : ℕ} (R : Fin m → List (Fin n)) : Prop :=
  (∀ k, R k ≠ []) ∧ List.Perm (List.ofFn R).flatten (List.finRange n)

/-- Feasibility in the distributionally robust CVRP RVRP(𝒫) (p. 719): `R ∈ 𝔓(V_C, m)` and
`ℙ[∑_{i ∈ R_k} q̃_i ≤ Q] ≥ 1 - ε` for every `ℙ ∈ 𝒫` and every vehicle `k`. -/
def RVRPFeasible {n m : ℕ} (Amb : Set (Measure (Fin n → ℝ))) (ε Q : ℝ)
    (R : Fin m → List (Fin n)) : Prop :=
  IsRouteSet R ∧ ∀ k, ∀ P ∈ Amb, ENNReal.ofReal (1 - ε) ≤ P {q | ((R k).map q).sum ≤ Q}

/-- Feasibility in the deterministic CVRP with vehicle capacity `Q` and demands `q` (p. 719):
`R ∈ 𝔓(V_C, m)` and `R_k ∈ ℛ(q)`, i.e. `∑_{i ∈ R_k} q_i ≤ Q`, for every vehicle `k`. -/
def DetFeasible {n m : ℕ} (Q : ℝ) (q : Fin n → ℝ) (R : Fin m → List (Fin n)) : Prop :=
  IsRouteSet R ∧ ∀ k, ((R k).map q).sum ≤ Q

end DRCVRP.Covariance


