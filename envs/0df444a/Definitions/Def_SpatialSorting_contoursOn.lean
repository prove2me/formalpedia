-- Prove2me | Definitions.Def_SpatialSorting_contoursOn
-- name    : SpatialSorting_contoursOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:42:58.178719+00:00
-- url     : https://prove2.me/theorems/1cba7e19-1cdc-4c34-a1fb-3cc1ca57dd76
-- title:
--   The contour set $\Gamma(\omega)$
-- statement:
--   For an assignment $\omega$, the contour set $\Gamma(\omega)=\{\gamma_1,\dots,\gamma_k\}$ consists of the contours $\gamma_i=(\overline\gamma_i,\omega|_{\overline\gamma_i})$, where $\overline\gamma_1,\dots,\overline\gamma_k$ are the connected components of the subgraph induced on $\overline\Gamma(\omega)$.
--
--   **Formalization Note** Computed as the image of the bichromatic sites of a finite set $W$ under "the contour through this site". In the mission $W\supseteq\overline\Gamma(\omega)$ always holds: $W=D_L$ for a configuration of $\Omega_{D_L}$ extended by $0$, and $W=V\cup\partial_{\rm ext}V$ for a regional configuration on $V$ extended by its collar colour.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (Contours and contour sets), p. 14 (PDF p. 15)

import Mathlib
import Definitions.Def_SpatialSorting_Contour
import Definitions.Def_SpatialSorting_bad
import Definitions.Def_SpatialSorting_contourAt
open Classical Filter Topology

namespace SpatialSorting

/-- The contour set `Γ(ω)`: the contours through the bichromatic sites, computed inside a finite set `W ⊇ Γ̄(ω)`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (Contours and contour sets), p. 14 (PDF p. 15). -/
noncomputable def contoursOn {q : ℕ} [NeZero q] (W : Finset (ℤ × ℤ)) (ω : ℤ × ℤ → Fin q) :
    Finset (Contour q) :=
  (W.filter (fun u => u ∈ bad ω)).image (contourAt W ω)

end SpatialSorting


