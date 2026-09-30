-- Prove2me | Definitions.Def_DRCVRP_Marginal_Routing
-- name    : DRCVRP_Marginal_Routing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:38:02.9024+00:00
-- url     : https://prove2.me/theorems/f15029f2-edce-4e83-a6d0-fd6fe0a3d1a2
-- title:
--   Route sets $\mathfrak P(V_C,m)$ and feasibility in the deterministic CVRP and in RVRP($\mathcal P$)
-- statement:
--   Consider a depot and customers $V_C=\{1,\dots,n\}$, served by $m$ vehicles $K=\{1,\dots,m\}$ of capacity $Q\in\mathbb R_+$.
--
--   1. **Route sets.** $\mathfrak P(V_C,m)$ is the set of ordered partitions $\mathbf R=(R_1,\dots,R_m)$ of $V_C$ into $m$ nonempty, mutually disjoint, collectively exhaustive routes, each route $R_k=(R_{k,1},\dots,R_{k,n_k})$ an ordered list of customers (the route starts and ends at the depot).
--
--   2. **Deterministic CVRP feasibility.** For known demands $\boldsymbol q\in\mathbb R^n$, a route set is feasible if $\mathbf R\in\mathfrak P(V_C,m)$ and
--   $$
--   \mathbf R_k\in\mathcal R(\boldsymbol q),\ \text{ i.e. }\ \sum_{i\in R_k}q_i\le Q,\qquad\forall k\in K.
--   $$
--
--   3. **RVRP($\mathcal P$) feasibility.** For an ambiguity set $\mathcal P$ of distributions of the random demand vector $\tilde{\boldsymbol q}$ and $\epsilon\in(0,1)$, a route set is feasible if $\mathbf R\in\mathfrak P(V_C,m)$ and
--   $$
--   \mathbb P\big[\mathbf R_k\in\mathcal R(\tilde{\boldsymbol q})\big]\ge1-\epsilon\qquad\forall\mathbb P\in\mathcal P,\ \forall k\in K.
--   $$
--
--   Both problems minimize the same transportation cost $c(\mathbf R)$ over their feasible route sets, so they are equivalent exactly when their feasible sets coincide.
--
--   **Formalization Note** Customers are `Fin n` (0-based), vehicles `Fin m`, and a route is a `List (Fin n)` of the customers it visits in order (the depot at both ends is implicit, since costs are not needed here). `IsRouteSet R` says that every route is nonempty and that the concatenation of the routes is a permutation of all customers, i.e. every customer occurs exactly once. The capacity constraint of route `k` is `((R k).map q).sum ≤ Q`, and the chance constraint is `ENNReal.ofReal (1 - ε) ≤ P {q | ((R k).map q).sum ≤ Q}`.
-- source:
--   Ghosal and Wiesemann, The Distributionally Robust Chance-Constrained Vehicle Routing Problem, Oper. Res. 68(3) (2020) 716–732, §2, p. 718 (route sets 𝔓(V_C, m)), p. 719 (deterministic CVRP, RVRP(𝒫))

import Mathlib

open MeasureTheory

namespace DRCVRP.Marginal

/-!
The route-set layer of Ghosal and Wiesemann, *The Distributionally Robust Chance-Constrained
Vehicle Routing Problem*, Oper. Res. 68(3) (2020), §2, pp. 718–719, as far as Corollary 1 needs
it. Customers are `Fin n` (0-based), vehicles `Fin m`; a route is the ordered list of the
customers it visits (the depot at both ends is implicit). Costs are not needed: the deterministic
CVRP and RVRP(𝒫) minimize the same cost `c(R)` over route sets.
-/

/-- `R ∈ 𝔓(V_C, m)` (p. 718): `R = (R_1, …, R_m)` is an ordered partition of the customer set
into `m` nonempty ordered routes; every customer occurs exactly once across all routes. -/
def IsRouteSet {n m : ℕ} (R : Fin m → List (Fin n)) : Prop :=
  (∀ k, R k ≠ []) ∧ List.Perm (List.ofFn R).flatten (List.finRange n)

/-- Feasibility in the deterministic CVRP with customer demands `d` and capacity `Q` (p. 719):
`R ∈ 𝔓(V_C, m)` and `R_k ∈ ℛ(d)`, i.e. `∑_{i ∈ R_k} d_i ≤ Q`, for every vehicle `k`. -/
def CVRPFeasible {n m : ℕ} (d : Fin n → ℝ) (Q : ℝ) (R : Fin m → List (Fin n)) : Prop :=
  IsRouteSet R ∧ ∀ k, ((R k).map d).sum ≤ Q

/-- Feasibility in RVRP(𝒫) (p. 719): `R ∈ 𝔓(V_C, m)` and `ℙ[R_k ∈ ℛ(q̃)] ≥ 1 - ε` for every
`ℙ ∈ 𝒫` and every vehicle `k`, where `R_k ∈ ℛ(q)` means `∑_{i ∈ R_k} q_i ≤ Q`. -/
def RVRPFeasible {n m : ℕ} (Amb : Set (Measure (Fin n → ℝ))) (ε Q : ℝ)
    (R : Fin m → List (Fin n)) : Prop :=
  IsRouteSet R ∧ ∀ P ∈ Amb, ∀ k, ENNReal.ofReal (1 - ε) ≤ P {q | ((R k).map q).sum ≤ Q}

end DRCVRP.Marginal


