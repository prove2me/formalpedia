-- Prove2me | Definitions.Def_SpatialSorting_comps
-- name    : SpatialSorting_comps
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:43:09.272048+00:00
-- url     : https://prove2.me/theorems/74191b6b-6948-40db-a602-4bb57eda3720
-- title:
--   The complementary components $V_k$ of a scaffold
-- statement:
--   For a family $\mathcal S$ of contours with supports in $D_L$, the connected components $V_0,\dots,V_r$ of $D_L\setminus\overline{\mathcal S}$.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Definition 3.8, p. 19 (PDF p. 20)

import Mathlib
import Definitions.Def_SpatialSorting_D
import Definitions.Def_SpatialSorting_Contour
import Definitions.Def_SpatialSorting_supp
import Definitions.Def_SpatialSorting_components
open Classical Filter Topology

namespace SpatialSorting

/-- The connected components `V_0, …, V_r` of `D_L \ 𝒮̄`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Definition 3.8, p. 19 (PDF p. 20). -/
noncomputable def comps {q : ℕ} [NeZero q] (L : ℕ) (S : Finset (Contour q)) :
    Finset (Finset (ℤ × ℤ)) :=
  components (D L \ supp S)

end SpatialSorting


