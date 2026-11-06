-- Prove2me | Definitions.Def_SpatialSorting_ReachIn
-- name    : SpatialSorting_ReachIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:40:32.282916+00:00
-- url     : https://prove2.me/theorems/37e51b7c-e752-458e-aff4-b070aa34164b
-- title:
--   Reachability inside a set of sites
-- statement:
--   For a set $S$ of sites and sites $u,v$, $u$ *reaches* $v$ inside $S$ when there is a walk $u=x_0\sim x_1\sim\dots\sim x_n=v$ of the triangular lattice with every $x_k\in S$. In particular $u$ reaches itself inside $S$ exactly when $u\in S$.
--
--   The connected components of the subgraph of $\Lambda^\infty$ induced on $S$ are the classes of this relation; every component, contour support, complementary component and connectedness claim of the mission is phrased through it.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (connected components, §3), p. 14 (PDF p. 15)

import Mathlib
import Definitions.Def_SpatialSorting_tri
open Classical Filter Topology

namespace SpatialSorting

/-- `ReachIn S u v`: there is a walk of `Λ^∞` from `u` to `v` all of whose sites lie in `S`. Connected components of the subgraph induced on `S` are the classes of this relation.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (connected components, §3), p. 14 (PDF p. 15).

Formalization Note: The walk is a `SimpleGraph.Walk` of `tri`; the condition is on `Walk.support`, which includes both endpoints. -/
def ReachIn (S : Set (ℤ × ℤ)) (u v : ℤ × ℤ) : Prop :=
  ∃ w : tri.Walk u v, ∀ x ∈ w.support, x ∈ S

end SpatialSorting


