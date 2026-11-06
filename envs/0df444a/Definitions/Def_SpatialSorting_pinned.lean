-- Prove2me | Definitions.Def_SpatialSorting_pinned
-- name    : SpatialSorting_pinned
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:40:56.423425+00:00
-- url     : https://prove2.me/theorems/456a7c08-e5bd-46a6-93e2-c0bb2f76cc57
-- title:
--   The pinned collar $F(V)$
-- statement:
--   For a finite region $V$, the pinned collar is
--
--   $$F(V)=\{v\in V:\ d(v,V^c)\le2\},$$
--
--   the two layers of sites of $V$ within graph distance two of the complement. In the fixed-collar ensembles these sites carry the boundary colour.
--
--   **Formalization Note** $d(v,V^c)\le2$ is written as "some site outside $V$ is a neighbour of $v$ or a neighbour of a neighbour", so no graph-distance function is involved.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (Partition functions, §3), p. 16 (PDF p. 17)

import Mathlib
import Definitions.Def_SpatialSorting_tri
open Classical Filter Topology

namespace SpatialSorting

/-- `F(V) = {v ∈ V : d(v, V^c) ≤ 2}`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (Partition functions, §3), p. 16 (PDF p. 17). -/
noncomputable def pinned (V : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  V.filter (fun v => ∃ u, u ∉ V ∧ (tri.Adj v u ∨ ∃ w, tri.Adj v w ∧ tri.Adj w u))

end SpatialSorting


