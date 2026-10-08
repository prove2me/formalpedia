-- Prove2me | Definitions.Def_BNCovPack_Routing_Routing
-- name    : BNCovPack_Routing_Routing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T18:54:04.602982+00:00
-- url     : https://prove2.me/theorems/eab397aa-8866-4e7a-8d0b-7a41a9032d4e
-- title:
--   Feasible fractional routings of an online request sequence (Fig. 3)
-- statement:
--   Let $E$ be a finite set of edges with capacities $u : E \to \mathbb{R}$. A **request** $r_i$ is given by the finite list $\mathcal P(r_i)$ of its admissible paths, each path being a finite set of edges; requests arrive in a sequence $\sigma = (r_1, \dots, r_n)$. A **fractional routing** of $\sigma$ assigns a flow value $f(r_i, P)$ to each path $P \in \mathcal P(r_i)$ of each request.
--
--   The **load** of an edge $e$ is the total flow through it, and the **value** of the routing is its total flow:
--
--   $$
--   F_e(f) = \sum_{r_i} \sum_{P \in \mathcal P(r_i),\, e \in P} f(r_i, P), \qquad \mathrm{val}(f) = \sum_{r_i} \sum_{P \in \mathcal P(r_i)} f(r_i, P).
--   $$
--
--   The routing is **feasible** (the packing side of Fig. 3 of the paper) when
--
--   1. $f(r_i, P) \ge 0$ for every request and path;
--   2. every request receives total flow $\sum_{P \in \mathcal P(r_i)} f(r_i, P) \le 1$;
--   3. every edge respects its capacity, $F_e(f) \le u(e)$.
--
--   The maximum of $\mathrm{val}(f)$ over feasible routings is the fractional optimum of the online throughput-maximization (virtual-circuit routing) problem, against which the online algorithms of the mission are measured.
--
--   **Formalization Note** The request sequence is a `List (List (Finset E))` and a routing is a `List (List ℝ)` of the same shape (one entry per path, in order); the shape condition is part of feasibility. In the paper $\mathcal P(r_i)$ is the set of simple $s_i$–$t_i$ paths of a graph; here any finite family of edge sets is allowed, which contains the graph case.
-- source:
--   Buchbinder, Naor, Online Primal-Dual Algorithms for Covering and Packing, Math. Oper. Res. (2009), DOI 10.1287/moor.1080.0363, p. 14, Section 5.2, Figure 3

import Mathlib

namespace BNCovPack.Routing

/-! Fractional routings of a sequence of requests (Buchbinder–Naor 2009, §5.2, p. 14, Fig. 3).

The edge set is a finite type `E`. A request `r_i` is given by the list of its admissible paths
`P(r_i)`, each path being a finite set of edges. The arrival sequence of requests is a
`List (List (Finset E))`. A fractional routing assigns to the `j`-th path of the `i`-th request a
flow value `f(r_i, P)`; it is stored as a `List (List ℝ)` of the same shape. -/

/-- `pathLoad e ps fs = ∑_{j : e ∈ ps[j]} fs[j]`: the flow through edge `e` on the paths `ps` of a
single request, when path `ps[j]` carries flow `fs[j]` (lists are traversed in parallel). -/
def pathLoad {E : Type*} [DecidableEq E] (e : E) : List (Finset E) → List ℝ → ℝ
  | P :: ps, y :: ys => (if e ∈ P then y else 0) + pathLoad e ps ys
  | _, _ => 0

/-- `edgeLoad e σ f = ∑_{r_i} ∑_{P ∈ P(r_i) | e ∈ P} f(r_i, P)`: the total flow through edge `e`
(the left-hand side of the capacity constraint of Fig. 3). -/
def edgeLoad {E : Type*} [DecidableEq E] (e : E) : List (List (Finset E)) → List (List ℝ) → ℝ
  | ps :: σ, fs :: f => pathLoad e ps fs + edgeLoad e σ f
  | _, _ => 0

/-- The value `∑_{r_i} ∑_{P ∈ P(r_i)} f(r_i, P)` of a fractional routing (the objective of
Fig. 3). -/
def routingValue (f : List (List ℝ)) : ℝ :=
  (f.map List.sum).sum

/-- `f` is a feasible fractional routing of the request sequence `σ` with capacities `u`
(Fig. 3, p. 14):
1. `f` has the shape of `σ` (one flow value per path of each request) and is non-negative;
2. every request receives total flow `∑_{P ∈ P(r_i)} f(r_i, P) ≤ 1`;
3. every edge carries total flow at most its capacity, `edgeLoad e σ f ≤ u e`. -/
def IsFeasibleRouting {E : Type*} [DecidableEq E] (u : E → ℝ) (σ : List (List (Finset E)))
    (f : List (List ℝ)) : Prop :=
  List.Forall₂ (fun ps fs => fs.length = ps.length ∧ ∀ y ∈ fs, 0 ≤ y) σ f ∧
  (∀ fs ∈ f, fs.sum ≤ 1) ∧
  ∀ e, edgeLoad e σ f ≤ u e

end BNCovPack.Routing


