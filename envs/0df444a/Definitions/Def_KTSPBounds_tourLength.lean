-- Prove2me | Definitions.Def_KTSPBounds_tourLength
-- name    : KTSPBounds_tourLength
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:37:31.839668+00:00
-- url     : https://prove2.me/theorems/720844d2-0c21-4f2a-afe2-025dc6ddf01b
-- title:
--   The optimal tour length $l_{TSP}(X_1,\dots,X_n)$
-- statement:
--   The length of the optimal closed tour through $n$ points:
--
--   $$
--   l_{TSP}(x_1,\dots,x_n) = \min_{\pi} \Bigl( \sum_{i=1}^{n-1} \lvert x_{\pi(i+1)} - x_{\pi(i)} \rvert + \lvert x_{\pi(1)} - x_{\pi(n)} \rvert \Bigr),
--   $$
--
--   the minimum over all orderings $\pi$ of the points.
--
--   It is the objective (1) of the paper and is used by Lemma 1 and by the subpath averaging bound.
--
--   **Formalization Note** This is the published optimal tour cost `MetricTSP.tspOpt` for the Euclidean distances between the points. That definition carries no hypothesis on the costs.
-- source:
--   Blanchard, Jacquillat, Jaillet, Probabilistic bounds on the k-Traveling Salesman Problem and the Traveling Repairman Problem, arXiv:2211.11063v1, §2.1, eq. (1), p.4

import Mathlib
import Definitions.Def_MetricTSP_model
import Definitions.Def_KTSPBounds_Plane

namespace KTSPBounds

/-- The length `l_TSP(X_1, …, X_n)` of the optimal closed TSP tour through the points `x 0, …,
x (n-1)` (objective (1), p.4), Blanchard, Jacquillat, Jaillet, arXiv:2211.11063v1: the published optimal tour cost
`MetricTSP.tspOpt` for the Euclidean distances between the points.

**Formalization Note.** `MetricTSP.tspOpt` is the infimum, over orderings of the cities, of the
closed tour cost, and carries no hypothesis on the costs. For `n = 2` the tour traverses the one
edge twice, as (1) does: `|x_2 - x_1| + |x_1 - x_2|`. -/
noncomputable def tourLength {n : ℕ} (x : Fin n → Plane) : ℝ :=
  MetricTSP.tspOpt fun i j => dist (x i) (x j)

end KTSPBounds


