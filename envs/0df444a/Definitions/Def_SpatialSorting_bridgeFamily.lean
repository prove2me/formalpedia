-- Prove2me | Definitions.Def_SpatialSorting_bridgeFamily
-- name    : SpatialSorting_bridgeFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:51:41.506895+00:00
-- url     : https://prove2.me/theorems/9d122ed6-71d4-4b71-a1cd-9c167e1918fc
-- title:
--   The boundary-rooted selection $\mathcal S(\sigma)$
-- statement:
--   $\mathcal S(\sigma)=\mathcal S_{C^*(\sigma)}$, the contours of $\sigma$ meeting the selected columns. The construction is deterministic, so $\mathcal S(\sigma)$ is a function of $\sigma$.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 7.3, p. 43 (PDF p. 44)

import Mathlib
import Definitions.Def_SpatialSorting_Coloring
import Definitions.Def_SpatialSorting_Contour
import Definitions.Def_SpatialSorting_selected
import Definitions.Def_SpatialSorting_bridgeColumns
open Classical Filter Topology

namespace SpatialSorting

/-- `𝒮(σ) = 𝒮_{C^*}`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 7.3, p. 43 (PDF p. 44). -/
noncomputable def bridgeFamily {q : ℕ} [NeZero q] (δ : ℝ) (L : ℕ) (σ : Coloring q L) :
    Finset (Contour q) :=
  selected σ (bridgeColumns δ L σ)

end SpatialSorting


