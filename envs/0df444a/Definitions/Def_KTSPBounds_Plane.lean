-- Prove2me | Definitions.Def_KTSPBounds_Plane
-- name    : KTSPBounds_Plane
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:36:10.10223+00:00
-- url     : https://prove2.me/theorems/29e40ac6-6dc8-43d7-ab21-f1f468191aee
-- title:
--   The Euclidean plane $\mathbb R^2$
-- statement:
--   The plane $\mathbb R^2$ with its Euclidean distance, in which all points of this mission live.
--
--   This fixes the metric of every length below: the constants $2\pi$ and $2\sqrt n$ of the paper are constants of the Euclidean metric.
--
--   **Formalization Note** The type is `EuclideanSpace ℝ (Fin 2)`. The types `ℝ × ℝ` and `Fin 2 → ℝ` carry the sup metric and are not used.
-- source:
--   Blanchard, Jacquillat, Jaillet, Probabilistic bounds on the k-Traveling Salesman Problem and the Traveling Repairman Problem, arXiv:2211.11063v1, §2.1, p.4

import Mathlib

namespace KTSPBounds

/-- The Euclidean plane `ℝ²` of the paper (setup, §2.1, p.4: "the Euclidean space ℝ² equipped with
the natural Euclidean distance"), Blanchard, Jacquillat, Jaillet, arXiv:2211.11063v1.

**Formalization Note.** `EuclideanSpace ℝ (Fin 2)` carries the Euclidean distance. `ℝ × ℝ` and
`Fin 2 → ℝ` carry the sup metric, under which the constants `2π` and `2√n` of the paper change
meaning. -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

end KTSPBounds


