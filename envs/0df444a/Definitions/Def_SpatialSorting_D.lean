-- Prove2me | Definitions.Def_SpatialSorting_D
-- name    : SpatialSorting_D
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:39:33.737258+00:00
-- url     : https://prove2.me/theorems/03be4127-5e49-4e6e-9224-abbd8dcef1d3
-- title:
--   The rhombus $D_L$
-- statement:
--   For $L\ge 0$, the rhombus (finite diamond) is
--
--   $$D_L=\{(x,y)\in\mathbb Z^2:\ 0\le x,y\le L-1\}.$$
--
--   With the triangular-lattice embedding it is a Euclidean rhombus; the induced graph on $D_L$ is the finite diamond graph $\Lambda^L$ on which the model lives.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (The domain), p. 3 (PDF p. 4)

import Mathlib
open Classical Filter Topology

namespace SpatialSorting

/-- The rhombus `D_L = {(x, y) ∈ ℤ² : 0 ≤ x, y ≤ L − 1}`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (The domain), p. 3 (PDF p. 4). -/
noncomputable def D (L : ℕ) : Finset (ℤ × ℤ) := Finset.Ico (0 : ℤ) L ×ˢ Finset.Ico (0 : ℤ) L

end SpatialSorting


