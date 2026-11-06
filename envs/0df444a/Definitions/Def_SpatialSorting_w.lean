-- Prove2me | Definitions.Def_SpatialSorting_w
-- name    : SpatialSorting_w
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:45:28.96046+00:00
-- url     : https://prove2.me/theorems/e3cc8c84-a295-4d86-8054-1c4bacd5449c
-- title:
--   The physical contour weight $w_j(\gamma)$
-- statement:
--   For a contour $\gamma$ of type $j$,
--
--   $$w_j(\gamma)=e^{\|\gamma\|_{\beta,\mathbf h}}\prod_{j'\in\{0,1,\dots,q-1\}}\frac{Z_{j'}(\beta,\mathbf h,\mathrm{Int}_{j'}(\gamma))}{Z_j(\beta,\mathbf h,\mathrm{Int}_{j'}(\gamma))},$$
--
--   with the ordinary partition functions of the interiors. The weight depends on $\beta$ and $\mathbf h$.
--
--   **Formalization Note** The paper calls the definition recursive; with $Z_{j'}$ the ordinary fixed-collar sum it is a direct finite expression. An empty interior contributes the ratio $1$.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (Contour weights), p. 17 (PDF p. 18)

import Mathlib
import Definitions.Def_SpatialSorting_Contour
import Definitions.Def_SpatialSorting_intSet
import Definitions.Def_SpatialSorting_G
import Definitions.Def_SpatialSorting_Zord
open Classical Filter Topology

namespace SpatialSorting

/-- `w_j(γ) = e^{‖γ‖_{β,h}} Π_{j'} Z_{j'}(β, h, Int_{j'}(γ)) / Z_j(β, h, Int_{j'}(γ))`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (Contour weights), p. 17 (PDF p. 18). -/
noncomputable def w {q : ℕ} [NeZero q] (A : Matrix (Fin q) (Fin q) ℝ) (β : ℝ) (h : Fin q → ℝ)
    (j : Fin q) (γ : Contour q) : ℝ :=
  Real.exp (G A β h j γ) * ∏ j' : Fin q, Zord A β h j' (intSet j' γ) / Zord A β h j (intSet j' γ)

end SpatialSorting


