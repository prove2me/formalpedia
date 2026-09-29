-- Prove2me | Definitions.Def_SplitDeliveryVRPTW_Known_Solution
-- name    : SplitDeliveryVRPTW_Known_Solution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:49:51.316801+00:00
-- url     : https://prove2.me/theorems/9fe22837-0284-43ec-846b-9f8436377f96
-- title:
--   SDVRPTW routes, delivery patterns, solutions, cost, and optimality
-- statement:
--   Fix an SDVRPTW instance (capacity $Q$, demands $d_i$, time windows $[e_v, l_v]$, travel times $t_{vw}$, costs $c_{vw}$, arc set $\mathcal A$). This file defines routes, solutions and optimal solutions, following Desaulniers (2010, §1) and the arc-flow model (1)–(15) of §3.
--
--   A **route** is a walk $0 \to v_1 \to \dots \to v_m \to n+1$ whose customer sequence $(v_1, \dots, v_m)$ may repeat customers ($m = 0$ is the idle route $0 \to n+1$), together with
--
--   1. service start times $s_0, s_1, \dots, s_{m+1}$ at its positions, and
--   2. a quantity $q_k \ge 0$ delivered at the $k$-th customer visit $v_k$.
--
--   It is **feasible** if every consecutive pair of nodes is an arc of $\mathcal A$, every position is served inside its node's time window ($e \le s \le l$, both depot copies included), travel times are respected with waiting allowed ($s_{k} + t_{v_k v_{k+1}} \le s_{k+1}$), and the load respects the capacity: $\sum_k q_k \le Q$. Its **cost** is the sum of the costs $c$ of its arcs, and it delivers to customer $i$ the total $\sum_{k : v_k = i} q_k$.
--
--   A **solution** is a finite indexed family of feasible routes $r_1, \dots, r_m$, one per vehicle used ($m$ is unbounded, and two vehicles may drive the same walk). It is **feasible** if every customer receives at least its demand, constraint (2):
--   $$
--   \sum_{f=1}^{m} \mathrm{delivered}_f(i) \ \ge\ d_i \qquad \text{for all } i \in \mathcal N .
--   $$
--   Its cost is objective (1), the sum of its route costs, and it is **optimal** if it is feasible and its cost is at most the cost of every feasible solution. Finally, the number of traversals of a customer arc $(i, j)$ in a solution is the number of positions, summed over all routes, at which a visit to $i$ is immediately followed by a visit to $j$.
--
--   These are the objects about which the known properties of optimal SDVRPTW solutions (Theorem 1, Corollaries 1–2 and Remark 1 of the paper) are stated.
--
--   **Formalization Note** A route stores its customer list `visits : List (Fin n)`, a time function indexed by path position ($0$ = start depot, $k+1$ = the $k$-th visit, $m+1$ = end depot), and a quantity function indexed by visit position; values at unused indices play no role. Deliveries can only occur at visits, as constraint (14) requires. The per-vehicle upper bound $\bar d_i = \min\{d_i, Q\}$ of (14) is not imposed: it does not change the set of route patterns of feasible solutions or their costs. Demand satisfaction uses $\ge$ as in (2); replacing it by $=$ gives the same feasible route patterns. Solutions are indexed families `Fin m → Route I`, not sets, so duplicate routes are allowed, and optimality compares against every feasible solution with any number of routes; it does not presuppose that an optimum exists.
-- source:
--   Desaulniers, Branch-and-Price-and-Cut for the Split-Delivery Vehicle Routing Problem with Time Windows, Operations Research 58(1):179–192 (2010), https://doi.org/10.1287/opre.1090.0713, p. 179, Section 1 (routes, feasibility, cost); p. 182, Section 3, objective (1) and constraints (2), (7), (11)–(14)

import Mathlib
import Definitions.Def_SplitDeliveryVRPTW_Known_Instance

namespace SplitDeliveryVRPTW.Known

/-- The node sequence `0 → v₁ → ⋯ → v_m → n+1` of a route whose customer visits, in order,
are `vs = [v₁, …, v_m]`. The empty list gives the idle route `0 → n+1`. -/
def nodePath {n : ℕ} (vs : List (Fin n)) : List (Node n) :=
  Node.start :: (vs.map Node.cust ++ [Node.finish])

/-- A feasible route with its delivery pattern (Desaulniers 2010, §1, p. 179, and constraints
(11)–(14) of §3, p. 182). Customers may be visited several times (`visits` may repeat).
Positions in `nodePath visits` are numbered `0, …, visits.length + 1`:
* `time k` is the start time of service at the node in position `k`;
* `qty k` is the quantity delivered at the `k`-th customer visit, `visits[k]`
  (node position `k + 1`).
Feasibility: consecutive nodes are joined by arcs of 𝒜; every visited location, both depot
copies included, is served inside its time window; travel times are respected (waiting is
allowed); delivered quantities are nonnegative and their total does not exceed `Q`. -/
structure Route {n : ℕ} (I : Instance n) where
  visits : List (Fin n)
  qty : ℕ → ℝ
  time : ℕ → ℝ
  arcs_ok : ∀ k (h : k + 1 < (nodePath visits).length),
    I.IsArc (nodePath visits)[k] (nodePath visits)[k + 1]
  window_ok : ∀ k (h : k < (nodePath visits).length),
    I.e (nodePath visits)[k] ≤ time k ∧ time k ≤ I.l (nodePath visits)[k]
  travel_ok : ∀ k (h : k + 1 < (nodePath visits).length),
    time k + I.t (nodePath visits)[k] (nodePath visits)[k + 1] ≤ time (k + 1)
  qty_nonneg : ∀ k, k < visits.length → 0 ≤ qty k
  capacity_ok : ∑ k ∈ Finset.range visits.length, qty k ≤ I.Q

/-- Total quantity route `r` delivers to customer `i` (summed over all its visits to `i`). -/
def Route.delivered {n : ℕ} {I : Instance n} (r : Route I) (i : Fin n) : ℝ :=
  ∑ k ∈ Finset.range r.visits.length, if r.visits[k]? = some i then r.qty k else 0

/-- Cost of a route: the sum of the costs `c` of the arcs of its path `0 → ⋯ → n+1`. -/
def Route.cost {n : ℕ} {I : Instance n} (r : Route I) : ℝ :=
  ∑ k ∈ Finset.range (r.visits.length + 1),
    I.c ((nodePath r.visits).getD k .start) ((nodePath r.visits).getD (k + 1) .start)

/-- Number of times route `r` traverses the customer arc `(i, j)`, i.e. the number of
positions `k` with `visits[k] = i` and `visits[k+1] = j`. -/
def Route.arcCount {n : ℕ} {I : Instance n} (r : Route I) (i j : Fin n) : ℕ :=
  ((Finset.range r.visits.length).filter
    (fun k => r.visits[k]? = some i ∧ r.visits[k + 1]? = some j)).card

/-- A candidate SDVRPTW solution: a finite, indexed family of `m` feasible routes (one per
vehicle used; the number of vehicles is unlimited, and two vehicles may drive the same route). -/
structure Solution {n : ℕ} (I : Instance n) where
  m : ℕ
  routes : Fin m → Route I

/-- Demand satisfaction, constraint (2) (p. 182): every customer receives, summed over all
routes, at least its demand. -/
def Solution.Feasible {n : ℕ} {I : Instance n} (S : Solution I) : Prop :=
  ∀ i : Fin n, I.d i ≤ ∑ f, (S.routes f).delivered i

/-- Total cost of a solution, objective (1): the sum of its route costs. -/
def Solution.cost {n : ℕ} {I : Instance n} (S : Solution I) : ℝ :=
  ∑ f, (S.routes f).cost

/-- An optimal solution: feasible, and no more costly than any feasible solution. -/
def Solution.IsOptimal {n : ℕ} {I : Instance n} (S : Solution I) : Prop :=
  S.Feasible ∧ ∀ S' : Solution I, S'.Feasible → S.cost ≤ S'.cost

/-- Number of traversals of the customer arc `(i, j)`, summed over all routes of `S`
(the left-hand side of constraint (7) for a single arc). -/
def Solution.arcCount {n : ℕ} {I : Instance n} (S : Solution I) (i j : Fin n) : ℕ :=
  ∑ f, (S.routes f).arcCount i j

end SplitDeliveryVRPTW.Known


