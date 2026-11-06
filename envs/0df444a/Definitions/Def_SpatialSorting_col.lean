-- Prove2me | Definitions.Def_SpatialSorting_col
-- name    : SpatialSorting_col
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:41:03.175777+00:00
-- url     : https://prove2.me/theorems/57bce445-b2ce-4e23-b499-edf47c076eb5
-- title:
--   Columns $\mathrm{col}_c$
-- statement:
--   For $c\in\{0,\dots,L-1\}$, $\mathrm{col}_c=\{(c,y):0\le y\le L-1\}$, a full lattice column of the rhombus. Its endpoint $(c,0)$ lies in $\mathsf L_0\subseteq B_L$.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (§7.2), p. 43 (PDF p. 44)

import Mathlib
import Definitions.Def_SpatialSorting_D
open Classical Filter Topology

namespace SpatialSorting

/-- `col_c = {(c, y) : 0 ≤ y ≤ L − 1}`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (§7.2), p. 43 (PDF p. 44). -/
noncomputable def col (L c : ℕ) : Finset (ℤ × ℤ) := (D L).filter (fun v => v.1 = (c : ℤ))

end SpatialSorting


