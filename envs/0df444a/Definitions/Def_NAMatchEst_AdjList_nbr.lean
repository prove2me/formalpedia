-- Prove2me | Definitions.Def_NAMatchEst_AdjList_nbr
-- name    : NAMatchEst_AdjList_nbr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:50:25.910217+00:00
-- url     : https://prove2.me/theorems/17b7d6d7-6301-4cf4-a01d-9a076ebc1511
-- title:
--   The neighbour oracle $\mathrm{nbr}(v,i)$
-- statement:
--   The **neighbour oracle**: for a vertex $v$ and a natural number $i$,
--
--   $$
--   \mathrm{nbr}(v,i)=\begin{cases}\text{the $i$-th entry of the adjacency list of $v$}, & 1\le i\le \deg(v),\\ \bot, & \text{otherwise.}\end{cases}
--   $$
--
--   Indices are 1-based, as in the paper. Queries past the degree return $\bot$; the right-endpoint certification of the paper relies on this (a vertex of degree below $\Delta$ answers $\bot$ at positions $\deg(v)+1,\dots,\Delta$).
--
--   **Formalization Note** $\bot$ is `none`; entry $i$ is the list element at 0-based position $i-1$.
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §2.1, p.13 (PDF 17)

import Mathlib
import Definitions.Def_NAMatchEst_AdjList

namespace NAMatchEst

/-- The **neighbour oracle** `nbr(v, i)`: the `i`-th entry of the adjacency list of `v` when
`1 ≤ i ≤ deg(v)`, and `⊥` (here `none`) otherwise.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §2.1, p.13 (PDF 17): "Neighbor oracle: nbr(v, i) returns the i-th neighbor of v in the
adjacency list of v if 1 ⩽ i ⩽ deg(v), and returns ⊥ otherwise."

**Formalization Note** Indices are 1-based as in the source; entry `i` is the list element at
0-based position `i - 1` (the natural subtraction is guarded by `1 ≤ i`). -/
def AdjList.nbr {n : ℕ} (G : AdjList n) (v : Fin n) (i : ℕ) : Option (Fin n) :=
  if 1 ≤ i ∧ i ≤ (G.adj v).length then (G.adj v)[i - 1]? else none

end NAMatchEst


