-- Prove2me | Definitions.Def_LeGallBrownianMap_mapGH
-- name    : LeGallBrownianMap_mapGH
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:37:36.68206+00:00
-- url     : https://prove2.me/theorems/2ecff2e4-1584-4737-8e31-e000ac2a15a2
-- title:
--   The vertex set of a planar map with a scaled graph distance, as a point of $\mathbb K$
-- statement:
--   For a rooted planar map $M$ with vertex set $m$ and a constant $c>0$, $(m, c\, d_{gr})$ is the finite metric space of vertices with $c$ times the **graph distance** (the least number of edges of a path). This is the point of $\mathbb K$ given by its isometry class.
--
--   With $c = c_q n^{-1/4}$ this is the rescaled space $(m_n, c_q n^{-1/4} d_{gr})$ of Theorem 1.1.
--
--   **Formalization Note** Vertices are the orbits of the rotation permutation (`OAI.FKCRT.Vertex M`) and the graph is `OAI.FKCRT.graph M Set.univ`, in which loops are dropped and multiple edges merged; this changes no graph distance. A planar map is connected, so $c\,d_{gr}$ is a metric for $c>0$.
-- source:
--   Le Gall, Uniqueness and universality of the Brownian map, arXiv:1105.4842v2, §1, p.2 and Theorem 1.1, p.3

import Mathlib
import Definitions.Def_FKCRT
import Definitions.Def_LeGallBrownianMap_pseudoQuotientGH

open OAI.FKCRT GromovHausdorff

namespace LeGallBrownianMap

/-- Le Gall, *Uniqueness and universality of the Brownian map*, arXiv:1105.4842v2, §1, p.2:
"We denote the vertex set of M_n by m_n. We equip m_n with the graph distance d_gr, and we view
(m_n, d_gr) as a random variable taking values in the space K of isometry classes of compact
metric spaces", and Theorem 1.1, p.3: the rescaled space "(m_n, c_q n^{−1/4} d_gr)".

`mapGH c M` is the isometry class of the vertex set of the rooted planar map `M` equipped with
`c` times its graph distance.

**Formalization Note.** Vertices are the rotation orbits `OAI.FKCRT.Vertex M`; the graph is
`OAI.FKCRT.graph M Set.univ` (all edges; loops are dropped from adjacency and multiple edges
merged, which changes no graph distance). A map is connected, so for `c > 0` the function
`c · d_gr` is a metric on the finite vertex set and `pseudoQuotientGH` returns exactly its
isometry class. -/
noncomputable def mapGH {m : ℕ} (c : ℝ) (M : RootedMap m) : GHSpace :=
  pseudoQuotientGH (Vertex M) (fun v w => c * ((graph M Set.univ).dist v w : ℝ))

end LeGallBrownianMap


