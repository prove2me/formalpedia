-- Prove2me | Definitions.Def_TreeMultiflow_RatInstance_WellFormed
-- name    : TreeMultiflow_RatInstance_WellFormed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:01:24.390236+00:00
-- url     : https://prove2.me/theorems/ec9cba0e-8fef-4d02-b8dc-f7827673d8e2
-- title:
--   Well-formed rational instance
-- statement:
--   A rational instance is **well formed** if
--
--   1. every listed edge joins two different vertices with indices at most $n$ and has capacity at least $1$;
--   2. no two listed edges join the same pair of vertices;
--   3. every request has endpoint indices at most $n$ and a nonnegative weight;
--   4. the listed edges form a tree on $\{0,\dots,n\}$.
--
--   These are exactly the standing assumptions of Section 1 (a tree, integer capacities $u_e\ge 1$, nonnegative weights). Capacity-one edges next to larger ones, requests with equal endpoints, repeated requests and the one-vertex tree are all well formed. Feasibility of the fractional values is not part of this predicate.
-- source:
--   Harb, Improved Integrality Gap for Multicommodity Flow on Trees, arXiv:2609.07949, Section 1, p.2 (standing assumptions)

import Mathlib
import Definitions.Def_TreeMultiflow_RatInstance_graph

namespace TreeMultiflow

/-- **Well-formed rational instance.**
Harb, *Improved Integrality Gap for Multicommodity Flow on Trees*, arXiv:2609.07949, Section 1,
p.2: "Let T = (V, E) be a tree, and let uₑ ≥ 1 be an integer capacity for each edge e. … Each
request f ∈ F has a nonnegative weight w_f".

`I.WellFormed` says

1. every listed edge joins two different vertices with indices at most `I.n` and has capacity at
   least `1`;
2. no two listed edges join the same pair of vertices;
3. every request has endpoint indices at most `I.n` and a nonnegative weight;
4. the listed edges form a tree on `Fin (I.n + 1)`.

**Formalization Note.** Nothing else is excluded: capacity-one edges next to larger ones, requests
with equal endpoints, repeated requests and the one-vertex tree (`I.n = 0`) are all well formed.
Feasibility of the fractional values is not part of well-formedness; it is the hypothesis
`IsLPFeasible` of the theorems. -/
def RatInstance.WellFormed (I : RatInstance) : Prop :=
  (∀ t ∈ I.edges, t.1 ≤ I.n ∧ t.2.1 ≤ I.n ∧ t.1 ≠ t.2.1 ∧ 1 ≤ t.2.2) ∧
  (I.edges.map fun t => s(t.1, t.2.1)).Nodup ∧
  (∀ r ∈ I.reqs, r.1 ≤ I.n ∧ r.2.1 ≤ I.n ∧ 0 ≤ r.2.2.1) ∧
  I.graph.IsTree

end TreeMultiflow


