-- Prove2me | Definitions.Def_SpatialSorting_selected
-- name    : SpatialSorting_selected
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:46:38.299936+00:00
-- url     : https://prove2.me/theorems/6fa89a39-4e2e-4dc2-bf81-10b3edeeb137
-- title:
--   Contours meeting a set of columns $\mathcal S_C$
-- statement:
--   For a configuration $\sigma\in\Omega_{D_L}$ and a set $C$ of columns, $\mathcal S_C$ is the set of contours of $\sigma$ whose supports meet $\bigcup_{c\in C}\mathrm{col}_c$.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 7.3, p. 43 (PDF p. 44)

import Mathlib
import Definitions.Def_SpatialSorting_Coloring
import Definitions.Def_SpatialSorting_Contour
import Definitions.Def_SpatialSorting_contourSet
open Classical Filter Topology

namespace SpatialSorting

/-- `𝒮_C`: the contours of `σ` whose supports meet `⋃_{c ∈ C} col_c`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 7.3, p. 43 (PDF p. 44). -/
noncomputable def selected {q L : ℕ} [NeZero q] (σ : Coloring q L) (C : Finset ℕ) :
    Finset (Contour q) :=
  (contourSet σ).filter (fun γ => ∃ c ∈ C, ∃ v ∈ γ.support, v.1 = (c : ℤ))

end SpatialSorting


