-- Prove2me | Definitions.Def_SpatialSorting_contourSet
-- name    : SpatialSorting_contourSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:40.180422+00:00
-- url     : https://prove2.me/theorems/04770097-e995-4266-a753-d26f491a3d55
-- title:
--   The contour set $\Gamma(\sigma)$ of a configuration
-- statement:
--   For $\sigma\in\Omega_{D_L}$, extended by $0$ to $\Lambda^\infty$, $\Gamma(\sigma)$ is its set of contours. Its support $\overline\Gamma(\sigma)$ lies in $D_L\setminus\mathsf L_0$ (Eq. (13)), and $\mathcal H(\Gamma(\sigma))=H(\sigma)$.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (Contours and contour sets; p.19), p. 14 (PDF p. 15)

import Mathlib
import Definitions.Def_SpatialSorting_D
import Definitions.Def_SpatialSorting_I
import Definitions.Def_SpatialSorting_Coloring
import Definitions.Def_SpatialSorting_extendBy
import Definitions.Def_SpatialSorting_Contour
import Definitions.Def_SpatialSorting_contoursOn
open Classical Filter Topology

namespace SpatialSorting

/-- `Γ(σ)` for `σ ∈ Ω_{D_L}`, extended by 0 to `Λ^∞`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (Contours and contour sets; p.19), p. 14 (PDF p. 15). -/
noncomputable def contourSet {q L : ℕ} [NeZero q] (σ : Coloring q L) : Finset (Contour q) :=
  contoursOn (D L) (extendBy 0 (I L) σ)

end SpatialSorting


