-- Prove2me | Definitions.Def_DRCVRP_RCI_RouteSet
-- name    : DRCVRP_RCI_RouteSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:18:40.113705+00:00
-- url     : https://prove2.me/theorems/737a4dcf-891c-49f3-a588-11901a01b39a
-- title:
--   Route sets $\mathfrak P(V_C,m)$, their transportation cost, and the flow they induce
-- statement:
--   Consider a complete directed graph with nodes $V=\{0,1,\dots,n\}$ and arcs $A=\{(i,j)\in V\times V: i\neq j\}$. Node $0$ is the depot and $V_C=\{1,\dots,n\}$ is the set of customers; the depot hosts $m$ vehicles indexed by $K=\{1,\dots,m\}$, and traversing the arc $(i,j)$ costs $c(i,j)$.
--
--   A **route** is an ordered list $\mathbf R_k=(R_{k,1},\dots,R_{k,n_k})$ of customers. With the convention $R_{k,0}=R_{k,n_k+1}=0$ the vehicle starts and ends at the depot and traverses the arcs $(R_{k,l},R_{k,l+1})$, $l=0,\dots,n_k$. The set of **route sets** is
--   $$
--   \mathfrak P(V_C,m)=\Big\{(\mathbf R_1,\dots,\mathbf R_m):\ \mathbf R_k\neq\emptyset\ \forall k,\ \ \mathbf R_k\cap\mathbf R_l=\emptyset\ \forall k\neq l,\ \ \textstyle\bigcup_k\mathbf R_k=V_C\Big\},
--   $$
--   the ordered partitions of the customers into $m$ nonempty ordered routes. The **transportation cost** of a route set is
--   $$
--   c(\mathbf R)=\sum_{k\in K}\sum_{l=0}^{n_k}c(R_{k,l},R_{k,l+1}).
--   $$
--   A route set **induces** the 0/1 arc vector $x$ given by rule (3) of the paper:
--   $$
--   x_{ij}=1\iff \exists k\in K,\ \exists l\in\{0,\dots,n_k\}:\ (i,j)=(R_{k,l},R_{k,l+1}),
--   $$
--   and $x_{ij}=0$ otherwise. The cost of an arc vector is $\sum_{(i,j)\in A}c(i,j)\,x_{ij}$.
--
--   These objects are the two sides of the equivalence in Theorem 1: RVRP($\mathcal P$) optimizes over route sets, 2VF($\mathcal P$) over arc vectors, and (3) translates one into the other.
--
--   **Formalization Note** Customers are 0-based: the paper's customer $i$ is `i - 1 : Fin n`, and it is the graph node `(i - 1).succ : Fin (n+1)`; node `0` is the depot. Vehicles are `Fin m`. A route set is `R : Fin m → List (Fin n)`; `IsRouteSet R` requires every route nonempty and the concatenation of all routes to be a permutation of the list of all customers (so every customer occurs exactly once). `routeNodes r` is `0 :: r.map succ ++ [0]` and `routeArcs r` its consecutive pairs. Arc vectors are `Fin (n+1) → Fin (n+1) → ℕ`; `flowCost` sums over ordered pairs $i\neq j$ only.
-- source:
--   Ghosal and Wiesemann, The Distributionally Robust Chance-Constrained Vehicle Routing Problem, Oper. Res. 68(3) (2020) 716–732, §2, p. 718 (graph, 𝔓(V_C, m)), p. 719 (c(R), R_{k,0} = R_{k,n_k+1} = 0), §3, p. 720 (objective of 2VF(𝒫)), p. 722, Eq. (3)

import Mathlib

namespace DRCVRP.RCI

/-!
The graph and route-set layer of Ghosal and Wiesemann, *The Distributionally Robust
Chance-Constrained Vehicle Routing Problem*, Oper. Res. 68(3) (2020), §2, pp. 718–719.

Nodes are `Fin (n+1)`: node `0` is the depot and the paper's customer `i ∈ {1,…,n}` is the node
`i.succ` of the customer `i - 1 : Fin n` (0-based customers). Vehicles are `Fin m`.
-/

/-- The node list `(0, R_{k,1}, …, R_{k,n_k}, 0)` of a route `r = (R_{k,1}, …, R_{k,n_k})`:
the route starts and ends at the depot (`R_{k,0} = R_{k,n_k+1} = 0`, p. 719). -/
def routeNodes {n : ℕ} (r : List (Fin n)) : List (Fin (n + 1)) :=
  0 :: r.map Fin.succ ++ [0]

/-- The arcs `(R_{k,l}, R_{k,l+1})`, `l = 0, …, n_k`, traversed by a route. -/
def routeArcs {n : ℕ} (r : List (Fin n)) : List (Fin (n + 1) × Fin (n + 1)) :=
  (routeNodes r).zip (routeNodes r).tail

/-- `R ∈ 𝔓(V_C, m)` (p. 718): `R = (R_1, …, R_m)` is an ordered partition of the customer set
into `m` nonempty ordered routes; every customer occurs exactly once across all routes. -/
def IsRouteSet {n m : ℕ} (R : Fin m → List (Fin n)) : Prop :=
  (∀ k, R k ≠ []) ∧ List.Perm (List.ofFn R).flatten (List.finRange n)

/-- The transportation cost `c(R) = ∑_{k ∈ K} ∑_{l=0}^{n_k} c(R_{k,l}, R_{k,l+1})` (p. 719). -/
def routeSetCost {n m : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (R : Fin m → List (Fin n)) : ℝ :=
  ∑ k, ((routeArcs (R k)).map (fun a => c a.1 a.2)).sum

/-- The flow induced by a route set via (3) (Theorem 1, p. 722):
`x_ij = 1 ⟺ ∃ k ∈ K, ∃ l ∈ {0, …, n_k} : (i, j) = (R_{k,l}, R_{k,l+1})`, and `x_ij = 0`
otherwise. -/
def inducedFlow {n m : ℕ} (R : Fin m → List (Fin n)) (i j : Fin (n + 1)) : ℕ :=
  if ∃ k, (i, j) ∈ routeArcs (R k) then 1 else 0

/-- The cost `∑_{(i,j) ∈ A} c(i,j) x_ij` of a flow, over the arcs `A = {(i,j) : i ≠ j}` (p. 720). -/
def flowCost {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (x : Fin (n + 1) → Fin (n + 1) → ℕ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), c i j * (x i j : ℝ)

end DRCVRP.RCI


