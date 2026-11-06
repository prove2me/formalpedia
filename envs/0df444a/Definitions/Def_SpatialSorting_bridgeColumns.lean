-- Prove2me | Definitions.Def_SpatialSorting_bridgeColumns
-- name    : SpatialSorting_bridgeColumns
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:50:27.783171+00:00
-- url     : https://prove2.me/theorems/3f0528da-e128-45f3-8a16-7a7be4e7915f
-- title:
--   The final column set $C^*(\sigma)$
-- statement:
--   $C^*(\sigma)$ is the final set of the procedure of Lemma 7.3 started from $C=\emptyset$.
--
--   **Formalization Note** Computed as $L$ iterations of the step: each effective step adds a new column among $L$, so after $L$ steps no further column can be added and the procedure has stopped.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 7.3, p. 43 (PDF p. 44)

import Mathlib
import Definitions.Def_SpatialSorting_Coloring
import Definitions.Def_SpatialSorting_bridgeStep
open Classical Filter Topology

namespace SpatialSorting

/-- `C^*(σ)`: the result of the selection procedure started at `C = ∅`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 7.3, p. 43 (PDF p. 44). -/
noncomputable def bridgeColumns {q : ℕ} [NeZero q] (δ : ℝ) (L : ℕ) (σ : Coloring q L) :
    Finset ℕ :=
  (bridgeStep δ L σ)^[L] ∅

end SpatialSorting


