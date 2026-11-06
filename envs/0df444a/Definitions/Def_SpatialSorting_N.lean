-- Prove2me | Definitions.Def_SpatialSorting_N
-- name    : SpatialSorting_N
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:40:20.693574+00:00
-- url     : https://prove2.me/theorems/cbd66a68-76b1-4932-9aae-b0f73df71a87
-- title:
--   The number $N_L$ of free sites
-- statement:
--   $N_L=|I_L|$ is the number of free sites of the rhombus; for $L\ge4$, $N_L=(L-4)^2$. The prescribed colour counts are $\lfloor\rho_iN_L\rfloor$.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (The domain), p. 3 (PDF p. 4)

import Mathlib
import Definitions.Def_SpatialSorting_I
open Classical Filter Topology

namespace SpatialSorting

/-- `N_L = |I_L|`, the number of free sites.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (The domain), p. 3 (PDF p. 4). -/
noncomputable def N (L : ℕ) : ℕ := (I L).card

end SpatialSorting


