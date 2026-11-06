-- Prove2me | Definitions.Def_SpatialSorting_compLabel
-- name    : SpatialSorting_compLabel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:40:48.500559+00:00
-- url     : https://prove2.me/theorems/8526ad8e-5067-463a-8dc6-6946ddde746e
-- title:
--   The boundary label $i(I)$
-- statement:
--   For a contour $\gamma$ and a complementary component $J$, the label $i(J)$ is the common colour of the sites of $\overline\gamma$ adjacent to $J$. By Lemma 3.1 these sites all carry the same colour.
--
--   **Formalization Note** The colour of one chosen adjacent support site (and $0$ if there is none). For a contour, Lemma 3.1 makes the choice irrelevant.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 3.1; unnumbered (Truncated weights), p. 17 (PDF p. 18)

import Mathlib
import Definitions.Def_SpatialSorting_tri
import Definitions.Def_SpatialSorting_Contour
open Classical Filter Topology

namespace SpatialSorting

/-- The label `i(J)`: the colour of the support sites adjacent to `J`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 3.1; unnumbered (Truncated weights), p. 17 (PDF p. 18). -/
noncomputable def compLabel {q : ℕ} [NeZero q] (γ : Contour q) (J : Finset (ℤ × ℤ)) : Fin q :=
  if h : ∃ s ∈ γ.support, ∃ v ∈ J, tri.Adj s v then γ.color h.choose else 0

end SpatialSorting


