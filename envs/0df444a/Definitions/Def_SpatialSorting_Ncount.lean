-- Prove2me | Definitions.Def_SpatialSorting_Ncount
-- name    : SpatialSorting_Ncount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:42:02.15066+00:00
-- url     : https://prove2.me/theorems/3ed42e79-6a46-4a61-b6d1-507f6779ceca
-- title:
--   Scaffold colour counts $N_i(\mathcal S)$
-- statement:
--   $N_i(\mathcal S)=|\{v\in\overline{\mathcal S}:\omega_{\mathcal S}(v)=i\}|$ counts the colour-$i$ scaffold sites, including sites of $B_L$ on the support.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 3.11, Eq. (17), p. 22 (PDF p. 23)

import Mathlib
import Definitions.Def_SpatialSorting_Contour
import Definitions.Def_SpatialSorting_supp
import Definitions.Def_SpatialSorting_jointColor
open Classical Filter Topology

namespace SpatialSorting

/-- `N_i(𝒮)`, the number of colour-`i` sites of `𝒮̄`, wired sites included.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 3.11, Eq. (17), p. 22 (PDF p. 23). -/
noncomputable def Ncount {q : ℕ} [NeZero q] (S : Finset (Contour q)) (i : Fin q) : ℕ :=
  ((supp S).filter (fun v => jointColor S v = i)).card

end SpatialSorting


