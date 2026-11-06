-- Prove2me | Definitions.Def_SpatialSorting_B
-- name    : SpatialSorting_B
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:40:30.917294+00:00
-- url     : https://prove2.me/theorems/47803f7a-92b0-4914-b0f1-20ab0ee226d2
-- title:
--   The wired collar $B_L$
-- statement:
--   The wired boundary collar is $B_L=D_L\setminus I_L$, the two outer layers of the rhombus. Every site of $B_L$ carries colour $0$ in every configuration of the model; for $L\ge4$ one has $|B_L|=8L-16$.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (The domain), p. 3 (PDF p. 4)

import Mathlib
import Definitions.Def_SpatialSorting_D
import Definitions.Def_SpatialSorting_I
open Classical Filter Topology

namespace SpatialSorting

/-- The two-layer wired collar `B_L = D_L \ I_L`, pinned to colour 0.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (The domain), p. 3 (PDF p. 4). -/
noncomputable def B (L : ℕ) : Finset (ℤ × ℤ) := D L \ I L

end SpatialSorting


