-- Prove2me | Definitions.Def_SpatialSorting_boundedComps
-- name    : SpatialSorting_boundedComps
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:42:58.243163+00:00
-- url     : https://prove2.me/theorems/36efa92d-408f-4949-b536-8e9629a72ee4
-- title:
--   The bounded interiors $\mathcal I(\gamma)$
-- statement:
--   $\mathcal I(\gamma)$ is the set of individual bounded connected components $I$ of $\Lambda^\infty\setminus\overline\gamma$ (the interiors of $\gamma$), each a finite set of sites.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (Truncated weights), p. 17 (PDF p. 18)

import Mathlib
import Definitions.Def_SpatialSorting_ReachIn
import Definitions.Def_SpatialSorting_Contour
import Definitions.Def_SpatialSorting_filled
open Classical Filter Topology

namespace SpatialSorting

/-- `ℐ(γ)`, the individual bounded components of `Λ^∞ \ γ̄`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (Truncated weights), p. 17 (PDF p. 18). -/
noncomputable def boundedComps {q : ℕ} [NeZero q] (γ : Contour q) : Finset (Finset (ℤ × ℤ)) :=
  ((filled γ) \ γ.support).image
    (fun v => (filled γ).filter (fun w => ReachIn (↑γ.support)ᶜ v w))

end SpatialSorting


