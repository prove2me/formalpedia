-- Prove2me | Definitions.Def_SpatialSorting_labelGroup
-- name    : SpatialSorting_labelGroup
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:08.461251+00:00
-- url     : https://prove2.me/theorems/c13d9d6c-2c82-4254-8b09-aec8cf83f368
-- title:
--   The label groups $V^{(j)}$
-- statement:
--   For a scaffold with labels $j_k$ and a colour $j$, $V^{(j)}=\bigcup_{k:\,j_k=j}V_k$ is the union of the complementary components with label $j$. It may be disconnected and may have holes.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Corollary 3.13, p. 23 (PDF p. 24)

import Mathlib
import Definitions.Def_SpatialSorting_Contour
import Definitions.Def_SpatialSorting_comps
open Classical Filter Topology

namespace SpatialSorting

/-- `V^{(j)} = ⋃_{k : j_k = j} V_k`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Corollary 3.13, p. 23 (PDF p. 24). -/
noncomputable def labelGroup {q : ℕ} [NeZero q] (L : ℕ) (S : Finset (Contour q))
    (lab : Finset (ℤ × ℤ) → Fin q) (j : Fin q) : Finset (ℤ × ℤ) :=
  ((comps L S).filter (fun V => lab V = j)).biUnion id

end SpatialSorting


