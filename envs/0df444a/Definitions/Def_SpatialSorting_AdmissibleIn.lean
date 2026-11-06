-- Prove2me | Definitions.Def_SpatialSorting_AdmissibleIn
-- name    : SpatialSorting_AdmissibleIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:42:58.831176+00:00
-- url     : https://prove2.me/theorems/a0cce21d-a28a-4840-bfba-54a77fd38284
-- title:
--   Admissibility in a region (Definition 3.5)
-- statement:
--   A finite contour $\gamma$ is admissible in a region $V$ if
--
--   $$F_\gamma\subseteq V\qquad\text{and}\qquad d(\overline\gamma,V^c)\ge2 .$$
--
--   This excludes a contour that surrounds a hole of $V$, even though the contour itself is planar.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Definition 3.5, p. 18 (PDF p. 19)

import Mathlib
import Definitions.Def_SpatialSorting_tri
import Definitions.Def_SpatialSorting_Contour
import Definitions.Def_SpatialSorting_filled
open Classical Filter Topology

namespace SpatialSorting

/-- Definition 3.5: `γ` is admissible in `V` if `F_γ ⊆ V` and `d(γ̄, V^c) ≥ 2`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Definition 3.5, p. 18 (PDF p. 19). -/
def AdmissibleIn {q : ℕ} [NeZero q] (V : Finset (ℤ × ℤ)) (γ : Contour q) : Prop :=
  filled γ ⊆ V ∧ ∀ s ∈ γ.support, ∀ u, u ∉ V → s ≠ u ∧ ¬ tri.Adj s u

end SpatialSorting


