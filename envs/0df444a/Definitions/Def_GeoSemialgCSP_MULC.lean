-- Prove2me | Definitions.Def_GeoSemialgCSP_MULC
-- name    : GeoSemialgCSP_MULC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:47:03.478386+00:00
-- url     : https://prove2.me/theorems/15b931fa-c6ee-4bd3-971e-9c5d660f7c12
-- title:
--   Unique Games instance with parallel edges
-- statement:
--   A **Unique Games instance** has a bipartite graph with left vertices $U$, right vertices $V$ and alphabet $[R]$; every edge occurrence $(u,v)$ carries a permutation $\pi_{uv}$ of $[R]$. Parallel edges are allowed and are distinguished as edge occurrences, each with its own permutation.
--
--   **Formalization Note** Left vertices `Fin nV`, right vertices `Fin nW`, alphabet `Fin M`; the edges are a list of triples $(u,v,\pi_{uv})$.
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), §6, p.17 (PDF p.18)

import Mathlib

namespace GeoSemialgCSP

/-- **Unique Label Cover with parallel edges.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), §6, printed p.17 (PDF p.18): a
bipartite constraint graph `(U, V, E)` with alphabet `[R]` and, for each edge, a permutation
`π_{uv}`; "parallel edges, if present, are distinguished as edge occurrences, each with its own
permutation".

**Formalization Note.** Left vertices `Fin nV`, right vertices `Fin nW`, labels `Fin M`; the edges
are a list of occurrences `(u, v, π_{uv})`. -/
structure MULC where
  /-- number of left vertices -/
  nV : ℕ
  /-- number of right vertices -/
  nW : ℕ
  /-- alphabet size -/
  M : ℕ
  /-- edge occurrences, each with its permutation -/
  edges : List (Fin nV × Fin nW × Equiv.Perm (Fin M))

end GeoSemialgCSP


