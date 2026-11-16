-- Prove2me | Definitions.Def_LEDPCount_Supplement_boundedDegree
-- name    : LEDPCount_Supplement_boundedDegree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:57:17.266044+00:00
-- url     : https://prove2.me/theorems/e5c4b40a-3c23-4099-aa3a-5971e46febf8
-- title:
--   The graph family $\mathcal G_{n,d}$ of graphs with maximum degree at most $d$
-- statement:
--   For natural numbers $n$ and $d$, $\mathcal G_{n,d}$ is the family of all simple undirected graphs $G$ on the vertex set $[n]$ whose **maximum degree** is at most $d$:
--   $$
--   \mathcal G_{n,d}=\bigl\{G=([n],E)\ :\ |N_G(v)|\le d\ \text{for every } v\in[n]\bigr\},
--   $$
--   where $N_G(v)$ is the set of neighbours of $v$. The degree-dependent lower bound (Theorem 5.3) is stated for algorithms whose inputs range over $\mathcal G_{n,d}$.
--
--   **Formalization Note** Graphs are simple graphs on $\mathrm{Fin}\,n=\{0,\dots,n-1\}$, as in the published `LEDPCount` definitions; the degree of $v$ is the cardinality (`Set.ncard`) of its finite neighbour set.
-- source:
--   Chen–Peng, The Power of Interaction in Locally Edge-Private Subgraph Counting, arXiv:2611.05038 (held version, sha256 d18032b0…), §2.1, p.13 (PDF p.15); Theorem 5.3, p.56 (PDF p.58)

import Mathlib

namespace LEDPCount.Supplement

/-- The graph family `G_{n,d}` (Chen–Peng, *The Power of Interaction in Locally Edge-Private
Subgraph Counting*, arXiv:2611.05038, held version sha256 d18032b0…, §2.1, p.13, PDF p.15): all
simple graphs on the vertex set `[n]` whose maximum degree is at most `d`, i.e. every vertex has at
most `d` neighbours.

**Formalization Note** Graphs are `SimpleGraph (Fin n)` (vertices `0, …, n−1`), as in the
published `LEDPCount` definitions; the degree of `v` is the cardinality of its (finite) neighbour
set. -/
def boundedDegree (n d : ℕ) : Set (SimpleGraph (Fin n)) :=
  {G | ∀ v : Fin n, (G.neighborSet v).ncard ≤ d}

end LEDPCount.Supplement


