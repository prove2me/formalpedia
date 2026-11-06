-- Prove2me | Definitions.Def_SpatialSorting_polymers
-- name    : SpatialSorting_polymers
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:29.339442+00:00
-- url     : https://prove2.me/theorems/77af4144-c338-4b40-b776-cd1accc255b9
-- title:
--   Polymer families $\mathcal P_j(V)$
-- statement:
--   $\mathcal P_j(V)$ is the set of finite families $\Gamma$ of type-$j$ contours that are admissible in $V$ and pairwise compatible. The empty family belongs to it.
--
--   Families need not be consistent: a type-$j$ contour may sit inside an interior of another member with a different label (p.15).
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (Contour weights); Lemma 3.6, p. 17 (PDF p. 18)

import Mathlib
import Definitions.Def_SpatialSorting_Contour
import Definitions.Def_SpatialSorting_IsContour
import Definitions.Def_SpatialSorting_IsType
import Definitions.Def_SpatialSorting_Compatible
import Definitions.Def_SpatialSorting_AdmissibleIn
import Definitions.Def_SpatialSorting_contoursIn
open Classical Filter Topology

namespace SpatialSorting

/-- `𝒫_j(V)`: finite families of pairwise compatible type-`j` contours admissible in `V`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (Contour weights); Lemma 3.6, p. 17 (PDF p. 18). -/
noncomputable def polymers {q : ℕ} [NeZero q] (j : Fin q) (V : Finset (ℤ × ℤ)) :
    Finset (Finset (Contour q)) :=
  ((contoursIn V).filter (fun γ => IsContour γ ∧ IsType j γ ∧ AdmissibleIn V γ)).powerset.filter
    (fun Γ => ∀ γ ∈ Γ, ∀ γ' ∈ Γ, γ ≠ γ' → Compatible γ γ')

end SpatialSorting


