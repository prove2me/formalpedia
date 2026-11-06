-- Prove2me | Definitions.Def_SpatialSorting_IsType
-- name    : SpatialSorting_IsType
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:42:34.231046+00:00
-- url     : https://prove2.me/theorems/c77d023b-31e1-4e30-a547-c41ed3566423
-- title:
--   Contours of type $j$, the class $\mathcal C_j$
-- statement:
--   A finite contour $\gamma$ has type $j$, written $\gamma\in\mathcal C_j$, when the label of its exterior $\mathrm{Ext}(\gamma)$ is $j$: every site of $\overline\gamma$ adjacent to $\mathrm{Ext}(\gamma)$ has colour $j$.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (§3, after Lemma 3.1; Contour weights), p. 15 (PDF p. 16)

import Mathlib
import Definitions.Def_SpatialSorting_tri
import Definitions.Def_SpatialSorting_Contour
import Definitions.Def_SpatialSorting_extSet
open Classical Filter Topology

namespace SpatialSorting

/-- `γ ∈ 𝒞_j`: the support sites adjacent to `Ext(γ)` have colour `j`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (§3, after Lemma 3.1; Contour weights), p. 15 (PDF p. 16). -/
def IsType {q : ℕ} [NeZero q] (j : Fin q) (γ : Contour q) : Prop :=
  ∀ s ∈ γ.support, ∀ v ∈ extSet γ, tri.Adj s v → γ.color s = j

end SpatialSorting


