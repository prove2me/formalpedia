-- Prove2me | Definitions.Def_SpatialSorting_vol
-- name    : SpatialSorting_vol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:42:43.405091+00:00
-- url     : https://prove2.me/theorems/da986f44-16a0-44af-b979-8069eefd8a1f
-- title:
--   The filled volume $v_\gamma$
-- statement:
--   $v_\gamma=|F_\gamma|$ is the number of sites of the filled support. The auxiliary activities are defined by induction on it.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (§C.2), p. 57 (PDF p. 58)

import Mathlib
import Definitions.Def_SpatialSorting_Contour
import Definitions.Def_SpatialSorting_filled
open Classical Filter Topology

namespace SpatialSorting

/-- `v_γ = |F_γ|`, the filled volume.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (§C.2), p. 57 (PDF p. 58). -/
noncomputable def vol {q : ℕ} [NeZero q] (γ : Contour q) : ℕ := (filled γ).card

end SpatialSorting


