-- Prove2me | Definitions.Def_SpatialSorting_jointColor
-- name    : SpatialSorting_jointColor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:41:00.45256+00:00
-- url     : https://prove2.me/theorems/ee28ef3d-1097-4d09-a427-c4aab126aec4
-- title:
--   The joint assignment $\omega_{\mathcal S}$
-- statement:
--   For a family $\mathcal S$ of contours with pairwise disjoint supports, $\omega_{\mathcal S}$ is the joint assignment on $\overline{\mathcal S}$: at a site of $\overline\gamma$, $\gamma\in\mathcal S$, it is $\omega_{\overline\gamma}$.
--
--   **Formalization Note** The colour of a chosen member containing the site, and $0$ off $\overline{\mathcal S}$; for a scaffold (W2) makes the member unique.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Definition 3.8, p. 19 (PDF p. 20)

import Mathlib
import Definitions.Def_SpatialSorting_Contour
open Classical Filter Topology

namespace SpatialSorting

/-- `ω_𝒮`: the joint assignment of a contour family on `𝒮̄`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Definition 3.8, p. 19 (PDF p. 20). -/
noncomputable def jointColor {q : ℕ} [NeZero q] (S : Finset (Contour q)) (v : ℤ × ℤ) : Fin q :=
  if h : ∃ γ ∈ S, v ∈ γ.support then h.choose.color v else 0

end SpatialSorting


