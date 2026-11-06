-- Prove2me | Definitions.Def_TreeMultiflow_RatInstance
-- name    : TreeMultiflow_RatInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:58:07.361936+00:00
-- url     : https://prove2.me/theorems/3cac79b9-fba4-4e32-80f4-059e10d39dfb
-- title:
--   Rationally encoded instance with a fractional solution
-- statement:
--   A **rationally encoded instance** consists of
--
--   1. a number $n$; the vertices are $0,1,\dots,n$;
--   2. a list of edges $(a,b,c)$: an edge between vertices $a$ and $b$ of integer capacity $c$;
--   3. a list of requests $(s,t,w,x)$: a request between $s$ and $t$ of rational weight $w$, together with its rational fractional value $x$.
--
--   Request $i$ is the $i$-th list entry, so repeated entries are distinct labeled requests. This is the input of the polynomial-time clauses of Theorems 1.2 and 2.1.
--
--   **Formalization Note** The vertex set is never empty. Whether the data form a tree with valid capacities and weights is a separate well-formedness predicate.
-- source:
--   Harb, Improved Integrality Gap for Multicommodity Flow on Trees, arXiv:2609.07949, Theorem 1.2, p.3 (rationally encoded inputs); Section 1, p.2 (the data)

import Mathlib

namespace TreeMultiflow

/-- **A rationally encoded instance of LP (1) with a fractional solution.**
Harb, *Improved Integrality Gap for Multicommodity Flow on Trees*, arXiv:2609.07949, Theorem 1.2,
p.3: "for rationally encoded inputs"; the data are those of Section 1, p.2 (a tree with integer
capacities, labeled requests with weights) and a fractional solution `x`.

* `n` : the vertices are `0, 1, …, n` (the type `Fin (n + 1)`);
* `edges` : a list of triples `(a, b, c)`, an edge between the vertices `a` and `b` of capacity
  `c`;
* `reqs` : a list of quadruples `(s, t, w, x)`, a request between `s` and `t` with weight `w` and
  fractional value `x`; request `i` is the `i`-th entry, so repeated entries are distinct labeled
  requests.

**Formalization Note.** The vertex set `Fin (n + 1)` is never empty, as a tree needs at least one
vertex. Whether the data really form a tree with valid capacities and weights is the predicate
`RatInstance.WellFormed`. -/
structure RatInstance where
  /-- the largest vertex index; vertices are `Fin (n + 1)` -/
  n : ℕ
  /-- edges `(a, b, capacity)` -/
  edges : List (ℕ × ℕ × ℕ)
  /-- requests `(s, t, weight, x)` -/
  reqs : List (ℕ × ℕ × ℚ × ℚ)

end TreeMultiflow


