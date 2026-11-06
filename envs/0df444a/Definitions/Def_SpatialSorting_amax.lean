-- Prove2me | Definitions.Def_SpatialSorting_amax
-- name    : SpatialSorting_amax
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:39:38.71455+00:00
-- url     : https://prove2.me/theorems/eb642adf-baf8-4da0-abb4-fe655d693be9
-- title:
--   The largest off-diagonal cost $A_{\max}$
-- statement:
--   For a cost matrix $A$, $A_{\max}=\max_{i\ne j}A(i,j)$ is its largest off-diagonal entry.
--
--   **Formalization Note** The maximum is over the ordered pairs $(i,j)$ with $i\ne j$; for $q\le1$ there are none and the value is set to $0$.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (§1.1), p. 2 (PDF p. 3)

import Mathlib
open Classical Filter Topology

namespace SpatialSorting

/-- `A_max`, the largest off-diagonal entry of `A`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (§1.1), p. 2 (PDF p. 3). -/
noncomputable def amax {q : ℕ} (A : Matrix (Fin q) (Fin q) ℝ) : ℝ :=
  if h : (Finset.univ : Finset (Fin q)).offDiag.Nonempty then
    (Finset.univ : Finset (Fin q)).offDiag.sup' h (fun p => A p.1 p.2) else 0

end SpatialSorting


