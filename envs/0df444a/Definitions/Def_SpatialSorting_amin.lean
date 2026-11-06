-- Prove2me | Definitions.Def_SpatialSorting_amin
-- name    : SpatialSorting_amin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:39:34.655193+00:00
-- url     : https://prove2.me/theorems/9f4f49c7-f681-410b-98e6-93ee7d7e55b6
-- title:
--   The smallest off-diagonal cost $A_{\min}$
-- statement:
--   For a cost matrix $A$, $A_{\min}=\min_{i\ne j}A(i,j)$ is its smallest off-diagonal entry.
--
--   **Formalization Note** The minimum is over the ordered pairs $(i,j)$ with $i\ne j$; for $q\le1$ there are none and the value is set to $0$. Every statement of the mission that uses it assumes $q\ge2$.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (§1.1), p. 2 (PDF p. 3)

import Mathlib
open Classical Filter Topology

namespace SpatialSorting

/-- `A_min`, the smallest off-diagonal entry of `A`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (§1.1), p. 2 (PDF p. 3). -/
noncomputable def amin {q : ℕ} (A : Matrix (Fin q) (Fin q) ℝ) : ℝ :=
  if h : (Finset.univ : Finset (Fin q)).offDiag.Nonempty then
    (Finset.univ : Finset (Fin q)).offDiag.inf' h (fun p => A p.1 p.2) else 0

end SpatialSorting


