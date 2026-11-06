-- Prove2me | Definitions.Def_SpatialSorting_intSet
-- name    : SpatialSorting_intSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:12.021506+00:00
-- url     : https://prove2.me/theorems/eef62e04-21dc-43b5-8592-f3130b0eb515
-- title:
--   The interiors $\mathrm{Int}_i(\gamma)$
-- statement:
--   For a colour $i$, $\mathrm{Int}_i(\gamma)$ is the union of the bounded complementary components of $\gamma$ with boundary label $i$ (Fig. 3). It may be empty.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (§3, after Lemma 3.1), p. 15 (PDF p. 16)

import Mathlib
import Definitions.Def_SpatialSorting_Contour
import Definitions.Def_SpatialSorting_boundedComps
import Definitions.Def_SpatialSorting_compLabel
open Classical Filter Topology

namespace SpatialSorting

/-- `Int_{j'}(γ)`: the union of the bounded complementary components of `γ` with label `j'`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (§3, after Lemma 3.1), p. 15 (PDF p. 16). -/
noncomputable def intSet {q : ℕ} [NeZero q] (j' : Fin q) (γ : Contour q) : Finset (ℤ × ℤ) :=
  ((boundedComps γ).filter (fun J => compLabel γ J = j')).biUnion id

end SpatialSorting


