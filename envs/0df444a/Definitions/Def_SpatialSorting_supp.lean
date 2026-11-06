-- Prove2me | Definitions.Def_SpatialSorting_supp
-- name    : SpatialSorting_supp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:40:51.543726+00:00
-- url     : https://prove2.me/theorems/ebcdf1b9-070c-4a67-802e-2b39691ffb13
-- title:
--   The support $\overline{\mathcal S}$ of a contour family
-- statement:
--   For a finite family $\mathcal S$ of contours, $\overline{\mathcal S}=\bigcup_{\gamma\in\mathcal S}\overline\gamma$ is the union of their supports. $|\overline{\mathcal S}|$ counts sites, whereas $\mathcal H(\mathcal S)$ is the weighted cost.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Definition 3.8, p. 19 (PDF p. 20)

import Mathlib
import Definitions.Def_SpatialSorting_Contour
open Classical Filter Topology

namespace SpatialSorting

/-- `𝒮̄ = ⋃_{γ ∈ 𝒮} γ̄`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Definition 3.8, p. 19 (PDF p. 20). -/
def supp {q : ℕ} [NeZero q] (Γ : Finset (Contour q)) : Finset (ℤ × ℤ) :=
  Γ.biUnion Contour.support

end SpatialSorting


