-- Prove2me | Definitions.Def_SparseMatchingDesign_density
-- name    : SparseMatchingDesign_density
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:14:38.326088+00:00
-- url     : https://prove2.me/theorems/4817f6db-bd0a-49f1-855a-3b63dc588680
-- title:
--   Density (average degree) $d(G)$ of a graph
-- statement:
--   The density, or average degree, of a finite graph $G$ with $|G|$ nodes is
--   $$d(G):=\frac{\sum_{v} d(v)}{|G|}=\frac{2|E|}{|G|},$$
--   where $d(v)$ is the number of neighbours of $v$. It measures how sparse a design is.
--
--   **Formalization Note** The degree is the cardinality of the neighbour set. The printed sum index "$v\in E$" is read as $v\in V$. For an empty node set the value is $0$; the paper's graphs have at least one node.
-- source:
--   Feng, Caldentey, Xin, Zhong, Wang, Hu, Designing Sparse Graphs for Stochastic Matching with an Application to Middle-Mile Transportation Management, SSRN 4123410 (Aug. 3, 2023), §2.1, p.4

import Mathlib

namespace SparseMatchingDesign

/-- The density (average degree) `d(G) := Σ_v d(v) / |G|` of a finite graph, with `d(v)` the
number of neighbours of `v`.

Feng, Caldentey, Xin, Zhong, Wang, Hu, *Designing Sparse Graphs for Stochastic Matching with an Application to Middle-Mile Transportation Management*, SSRN 4123410 (Aug. 3, 2023), §2.1, p.4: "We will denote by d(G) the average degree or density of a graph G = (V, E),
i.e., d(G) := Σ_{v∈E} d(v)/|G| = 2|E|/|G|."

**Formalization Note** The degree is `(G.neighborSet v).ncard`, which needs no decidability
instance. For the empty vertex type the value is `0 / 0 = 0`; the paper's graphs have `n ≥ 1`
nodes. (The printed "v ∈ E" in the sum is read as v ∈ V.) -/
noncomputable def density {V : Type*} [Fintype V] (G : SimpleGraph V) : ℝ :=
  (∑ v, ((G.neighborSet v).ncard : ℝ)) / Fintype.card V

end SparseMatchingDesign


