-- Prove2me | Definitions.Def_LEDPCount_EdgeNeighbors
-- name    : LEDPCount_EdgeNeighbors
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:05:29.924183+00:00
-- url     : https://prove2.me/theorems/150cdf3f-3dab-4a96-9ed3-1ff03244ac8b
-- title:
--   Edge-neighboring graphs (Definition 2.11)
-- statement:
--   Two graphs $G$ and $G'$ on the vertex set $[n]$ are **edge-neighboring**, written $G\sim G'$, if they differ in exactly one edge: the symmetric difference $E(G)\triangle E(G')$ consists of a single edge.
--
--   This is the neighbouring relation of edge differential privacy and of local edge differential privacy (Definition 2.13).
--
--   **Formalization Note** Graphs are simple graphs on $\mathrm{Fin}\,n$ and edges are unordered pairs.
-- source:
--   Chen–Peng, The Power of Interaction in Locally Edge-Private Subgraph Counting, arXiv:2611.05038 (held version, sha256 d18032b0…), Definition 2.11, p.16 (PDF p.18)

import Mathlib

namespace LEDPCount

/-- Definition 2.11 (Edge-Neighboring Graphs) (Chen–Peng, arXiv:2611.05038, held version sha256 d18032b0…, p.16, PDF p.18): two graphs
`G` and `G'` on `[n]` are edge-neighboring if they differ in exactly one edge, i.e. the
symmetric difference of their edge sets is a single edge.

**Formalization Note** Graphs are `SimpleGraph (Fin n)`; an edge is an element of
`Sym2 (Fin n)` (edge sets contain no diagonal pair). -/
def EdgeNeighbors {n : ℕ} (G G' : SimpleGraph (Fin n)) : Prop :=
  ∃ e : Sym2 (Fin n), symmDiff G.edgeSet G'.edgeSet = {e}

end LEDPCount


