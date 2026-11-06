-- Prove2me | Definitions.Def_SpatialSorting_components
-- name    : SpatialSorting_components
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:41:31.803241+00:00
-- url     : https://prove2.me/theorems/86ccd251-e4f6-4efa-b1c5-a1d86fd7e004
-- title:
--   The connected components of a region
-- statement:
--   The connected components $V_k$ of a finite set $V$ of sites (of the subgraph of $\Lambda^\infty$ induced on $V$), as a finite family of finite sets.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 4.6, p. 27 (PDF p. 28)

import Mathlib
import Definitions.Def_SpatialSorting_ReachIn
open Classical Filter Topology

namespace SpatialSorting

/-- The connected components `V_k` of a finite set `V` in `Λ^∞`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 4.6, p. 27 (PDF p. 28). -/
noncomputable def components (V : Finset (ℤ × ℤ)) : Finset (Finset (ℤ × ℤ)) :=
  V.image (fun u => V.filter (fun v => ReachIn ↑V u v))

end SpatialSorting


