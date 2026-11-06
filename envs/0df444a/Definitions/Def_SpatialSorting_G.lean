-- Prove2me | Definitions.Def_SpatialSorting_G
-- name    : SpatialSorting_G
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:43:37.387268+00:00
-- url     : https://prove2.me/theorems/c7447bd0-65c5-4d49-a065-bc180c2b2441
-- title:
--   The contour exponent $\|\gamma\|_{\beta,\mathbf h}$
-- statement:
--   For a type-$j$ contour,
--
--   $$\|\gamma\|_{\beta,\mathbf h}=G_j(\gamma;\mathbf h)=-\beta\mathcal H(\gamma)+\sum_{i}(h_i-h_j)N_i(\gamma),$$
--
--   the energy and field weight carried by the support relative to the background colour $j$.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (Contour weights); §C.2, p. 17 (PDF p. 18)

import Mathlib
import Definitions.Def_SpatialSorting_Contour
import Definitions.Def_SpatialSorting_cost
import Definitions.Def_SpatialSorting_Ncol
open Classical Filter Topology

namespace SpatialSorting

/-- `‖γ‖_{β,h} = G_j(γ; h) = −β ℋ(γ) + Σ_i (h_i − h_j) N_i(γ)`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (Contour weights); §C.2, p. 17 (PDF p. 18). -/
noncomputable def G {q : ℕ} [NeZero q] (A : Matrix (Fin q) (Fin q) ℝ) (β : ℝ) (h : Fin q → ℝ)
    (j : Fin q) (γ : Contour q) : ℝ :=
  -β * cost A γ + ∑ i, (h i - h j) * (Ncol γ i : ℝ)

end SpatialSorting


