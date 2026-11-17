-- Prove2me | Definitions.Def_MinrankTW_Supplement_thm7Input
-- name    : MinrankTW_Supplement_thm7Input
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:06:05.520865+00:00
-- url     : https://prove2.me/theorems/9c61b8f0-53ce-4311-97be-e968008180d7
-- title:
--   Input layout of Theorem 7: a graph and a target rank
-- statement:
--   The RAM input of Theorem 7: cell $0$ holds the number $n$ of vertices, cell $1$ the target rank $r$, and the next $n^2$ cells the adjacency bits of the graph, row by row; every other cell holds $0$. The graph is the simple graph whose edges are the pairs $\{u,v\}$, $u\ne v$, with a $1$ at $(u,v)$ or $(v,u)$.
--
--   It contains neither a fitting matrix nor a row basis: "Given only $G$, $\mathbb F_q$, and $r$".
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Theorem 7, p.22

import Mathlib

namespace MinrankTW.Supplement

/-- The RAM input of Theorem 7 (Perles–Weinstein, *Efficient Algorithms for Minrank and Index
Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991),
Theorem 7, p.22: "Given only G, F_q, and r"): cell `0` holds `n`, cell `1` holds the target rank
`r`, cells `2, …, 1 + n²` hold the bits `edge u v` row by row (`(u, v)` at offset `u·n + v`), and
every other cell holds `0`.

**Formalization Note** The graph is read as `SimpleGraph.fromRel` of `edge`, as in the published
`MinrankTW.thm1Input`; the field is fixed before the program. -/
def thm7Input (n r : ℕ) (edge : Fin n → Fin n → Bool) : ℕ → ℕ := fun k =>
  if k = 0 then n else if k = 1 then r else
  if h : k - 2 < n * n then
    (edge (finProdFinEquiv.symm ⟨k - 2, h⟩).1 (finProdFinEquiv.symm ⟨k - 2, h⟩).2).toNat
  else 0

end MinrankTW.Supplement


