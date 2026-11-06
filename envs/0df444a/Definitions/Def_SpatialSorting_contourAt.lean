-- Prove2me | Definitions.Def_SpatialSorting_contourAt
-- name    : SpatialSorting_contourAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:41:48.421089+00:00
-- url     : https://prove2.me/theorems/f1984fff-ac33-4d2b-bf51-dcfff224fbdb
-- title:
--   The contour of a configuration through a site
-- statement:
--   For an assignment $\omega$ and a site $u\in\overline\Gamma(\omega)$, the contour of $\omega$ through $u$ is $\gamma=(\overline\gamma,\omega|_{\overline\gamma})$ with $\overline\gamma$ the connected component of $\overline\Gamma(\omega)$ containing $u$.
--
--   **Formalization Note** The support is computed as the set of sites of a finite set $W$ reached from $u$ inside $\overline\Gamma(\omega)$. Whenever $W\supseteq\overline\Gamma(\omega)$, which holds in every use of the mission, this is the whole component.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (Contours and contour sets), p. 14 (PDF p. 15)

import Mathlib
import Definitions.Def_SpatialSorting_ReachIn
import Definitions.Def_SpatialSorting_Contour
import Definitions.Def_SpatialSorting_bad
open Classical Filter Topology

namespace SpatialSorting

/-- The contour of `ω` whose support is the component of `Γ̄(ω)` containing `u`, computed inside a finite set `W ⊇ Γ̄(ω)`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (Contours and contour sets), p. 14 (PDF p. 15). -/
noncomputable def contourAt {q : ℕ} [NeZero q] (W : Finset (ℤ × ℤ)) (ω : ℤ × ℤ → Fin q)
    (u : ℤ × ℤ) : Contour q where
  support := W.filter (fun v => ReachIn (bad ω) u v)
  color := fun v => if v ∈ W.filter (fun v => ReachIn (bad ω) u v) then ω v else 0
  color_off := fun _ hv => if_neg hv

end SpatialSorting


