-- Prove2me | Definitions.Def_SpatialSorting_nbhd
-- name    : SpatialSorting_nbhd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:39:43.337358+00:00
-- url     : https://prove2.me/theorems/21b539c8-97cb-465f-9c63-5adcac435a11
-- title:
--   A region with its outer neighbours
-- statement:
--   For a finite set $V$, the set of sites of $V$ together with all their lattice neighbours, that is $V\cup\partial_{\rm ext}V$. It is a finite set containing every bichromatic site of a regional configuration on $V$ extended by a constant colour.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (helper for $\partial_{\rm ext}$), p. 27 (PDF p. 28)

import Mathlib
open Classical Filter Topology

namespace SpatialSorting

/-- `V` together with every lattice neighbour of a site of `V` (a finite superset of `V ∪ ∂_ext V`).

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (helper for $\partial_{\rm ext}$), p. 27 (PDF p. 28). -/
noncomputable def nbhd (V : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  V ∪ V.biUnion (fun v => ({(1, 0), (-1, 0), (0, 1), (0, -1), (1, -1), (-1, 1)} :
    Finset (ℤ × ℤ)).image (v + ·))

end SpatialSorting


