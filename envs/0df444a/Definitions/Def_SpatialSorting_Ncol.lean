-- Prove2me | Definitions.Def_SpatialSorting_Ncol
-- name    : SpatialSorting_Ncol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:40:45.310765+00:00
-- url     : https://prove2.me/theorems/f01413a4-5e82-4cdf-8339-04cd8f13b00b
-- title:
--   Colour counts $N_i(\gamma)$ on a support
-- statement:
--   $N_i(\gamma)=|\{v\in\overline\gamma:\omega_{\overline\gamma}(v)=i\}|$, written $n_i(\sigma_{\overline\gamma})$ on p.17.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (§C.2), p. 57 (PDF p. 58)

import Mathlib
import Definitions.Def_SpatialSorting_Contour
open Classical Filter Topology

namespace SpatialSorting

/-- `N_i(γ)`, the number of colour-`i` sites on the support of `γ`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (§C.2), p. 57 (PDF p. 58). -/
noncomputable def Ncol {q : ℕ} [NeZero q] (γ : Contour q) (i : Fin q) : ℕ :=
  (γ.support.filter (fun v => γ.color v = i)).card

end SpatialSorting


