-- Prove2me | Definitions.Def_DRCVRP_FirstOrder_RouteSet
-- name    : DRCVRP_FirstOrder_RouteSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:58:31.849157+00:00
-- url     : https://prove2.me/theorems/9fb46a39-3cf1-4fdb-b011-acea3edcc194
-- title:
--   Route sets and feasibility in the deterministic and the distributionally robust CVRP
-- statement:
--   A depot serves the customers $V_C=\{1,\dots,n\}$ with $m$ vehicles of capacity $Q$. The set $\mathfrak P(V_C,m)$ consists of the ordered route sets $\mathbf R=(\mathbf R_1,\dots,\mathbf R_m)$, where each route $\mathbf R_k$ is a nonempty ordered list of customers and every customer lies on exactly one route:
--
--   $$
--   \mathfrak P(V_C,m)=\Bigl\{(\mathbf R_1,\dots,\mathbf R_m):\mathbf R_k\ne\emptyset\ \forall k,\ \mathbf R_k\cap\mathbf R_l=\emptyset\ \forall k\ne l,\ \textstyle\bigcup_k\mathbf R_k=V_C\Bigr\}.
--   $$
--
--   1. In the **deterministic CVRP** with demands $\boldsymbol q$, a route set $\mathbf R\in\mathfrak P(V_C,m)$ is feasible when $\sum_{i\in\mathbf R_k}q_i\le Q$ for every vehicle $k$.
--   2. In the **distributionally robust CVRP** $\mathrm{RVRP}(\mathcal P)$ with ambiguity set $\mathcal P$ and risk level $\epsilon$, a route set $\mathbf R\in\mathfrak P(V_C,m)$ is feasible when $\mathbb P\bigl[\sum_{i\in\mathbf R_k}\tilde q_i\le Q\bigr]\ge1-\epsilon$ for every $\mathbb P\in\mathcal P$ and every vehicle $k$.
--
--   Transportation costs do not affect which route sets are feasible, so they are omitted here. These notions are what Theorem 4 of the paper compares.
--
--   **Formalization Note** Customers are `Fin n` (0-based) and vehicles `Fin m`; a route set is `R : Fin m → List (Fin n)`, and "every customer lies on exactly one route" is the statement that the concatenation of the routes is a permutation of the list of all customers.
-- source:
--   Ghosal and Wiesemann, The Distributionally Robust Chance-Constrained Vehicle Routing Problem, Oper. Res. 68(3) (2020) 716–732, https://doi.org/10.1287/opre.2019.1924, §2, p. 718 (route sets 𝔓(V_C, m)) and p. 719 (deterministic CVRP and RVRP(𝒫))

import Mathlib

open MeasureTheory

namespace DRCVRP.FirstOrder

/-!
The route-set layer of Ghosal and Wiesemann, *The Distributionally Robust Chance-Constrained
Vehicle Routing Problem*, Oper. Res. 68(3) (2020), §2, pp. 718–719, as far as feasibility is
concerned (transportation costs play no role in which route sets are feasible). Customers are
`Fin n` (0-based), vehicles are `Fin m`, and a route is an ordered list of customers.
-/

/-- `R ∈ 𝔓(V_C, m)` (p. 718): `R = (R_1, …, R_m)` is an ordered partition of the customer set
into `m` nonempty ordered routes; every customer occurs exactly once across all routes. -/
def IsRouteSet {n m : ℕ} (R : Fin m → List (Fin n)) : Prop :=
  (∀ k, R k ≠ []) ∧ List.Perm (List.ofFn R).flatten (List.finRange n)

/-- Feasibility in the deterministic CVRP with capacity `Q` and demands `q` (p. 719):
`R ∈ 𝔓(V_C, m)` and `R_k ∈ ℛ(q)`, i.e. `∑_{i ∈ R_k} q_i ≤ Q`, for every vehicle `k`. -/
def IsDeterministicFeasible {n m : ℕ} (Q : ℝ) (q : Fin n → ℝ) (R : Fin m → List (Fin n)) :
    Prop :=
  IsRouteSet R ∧ ∀ k, ((R k).map q).sum ≤ Q

/-- Feasibility in the distributionally robust CVRP `RVRP(𝒫)` with capacity `Q`, ambiguity
set `Amb` and risk level `ε` (p. 719): `R ∈ 𝔓(V_C, m)` and `ℙ[R_k ∈ ℛ(q̃)] ≥ 1 − ε` for every
`ℙ ∈ 𝒫` and every vehicle `k`. -/
def IsRVRPFeasible {n m : ℕ} (Amb : Set (Measure (Fin n → ℝ))) (ε Q : ℝ)
    (R : Fin m → List (Fin n)) : Prop :=
  IsRouteSet R ∧ ∀ P ∈ Amb, ∀ k, ENNReal.ofReal (1 - ε) ≤ P {q | ((R k).map q).sum ≤ Q}

end DRCVRP.FirstOrder


