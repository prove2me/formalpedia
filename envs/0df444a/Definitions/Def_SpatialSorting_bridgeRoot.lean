-- Prove2me | Definitions.Def_SpatialSorting_bridgeRoot
-- name    : SpatialSorting_bridgeRoot
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:52:09.011076+00:00
-- url     : https://prove2.me/theorems/903bac35-7ebf-4792-9802-4b6a7b79fc06
-- title:
--   The bridge root $B(\sigma)$
-- statement:
--   $B(\sigma)=B_L\cup\bigcup_{c\in C^*(\sigma)}\mathrm{col}_c$, the wired collar together with the selected columns.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 7.3, p. 43 (PDF p. 44)

import Mathlib
import Definitions.Def_SpatialSorting_B
import Definitions.Def_SpatialSorting_Coloring
import Definitions.Def_SpatialSorting_col
import Definitions.Def_SpatialSorting_bridgeColumns
open Classical Filter Topology

namespace SpatialSorting

/-- `B(σ) = B_L ∪ ⋃_{c ∈ C^*} col_c`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 7.3, p. 43 (PDF p. 44). -/
noncomputable def bridgeRoot {q : ℕ} [NeZero q] (δ : ℝ) (L : ℕ) (σ : Coloring q L) :
    Finset (ℤ × ℤ) :=
  B L ∪ (bridgeColumns δ L σ).biUnion (col L)

end SpatialSorting


