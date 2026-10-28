-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Normalization
-- name    : KLSModular_FunctionalInequalities_Analysis_Convex_Normalization
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:56:32.777495+00:00
-- url     : https://prove2.me/theorems/c20810ec-8464-4452-b023-bf292cc5b276
-- title:
--   Simplex edge matrix and volume
-- statement:
--   For vertices $v_0,\ldots,v_n\in\mathbb{R}^n$, `simplexEdgeMatrix v` is the matrix whose column $j$ is $v_{j+1}-v_0$, and `simplexVolume v` is the absolute value of its determinant. The module supplies auxiliary facts about maximal-volume simplices, simplex coordinates, and inclusions between standard simplices, balls, and boxes.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def simplexEdgeMatrix {n : ℕ} (v : Fin (n + 1) → EuclideanSpace ℝ (Fin n)) :
--       Matrix (Fin n) (Fin n) ℝ :=
--     Matrix.of fun i j => (v j.succ - v 0) i
--   ```
--
--   **Module navigation**
--
--   Theorems in source order:
--
--   - [`exists_max_simplexEdgeMatrix_det`](https://prove2.me/theorems/20479a29-7d2f-4cb5-8d1b-e0dbc2e4e013)
--   - [`abs_simplexCoord_le_one_of_max`](https://prove2.me/theorems/8c17d6d3-6bb3-4149-817e-62c066eb1e35)
--   - [`closedBall_subset_stdSimplex_and_box_subset_closedBall`](https://prove2.me/theorems/13e62e66-a24e-43f3-9ca6-0687c2a3f734)
--   - [`exists_affine_normalization`](https://prove2.me/theorems/eaae9cde-a1a3-4aa1-8fc7-b6ed5d522bb4)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Normalization.lean) · `FunctionalInequalities.Analysis.Convex.Normalization` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Normalization.lean#L20-L27 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Normalization`, definition bundle `KLSModular_FunctionalInequalities_Analysis_Convex_Normalization`; the repository is private at upload time).

import Mathlib

noncomputable section
open Set Matrix
namespace FunctionalInequalities
namespace Analysis
/-- The edge matrix of a simplex with vertices `v 0, …, v n` in `ℝⁿ`: column `j` is `v (j+1) − v 0`. -/
def simplexEdgeMatrix {n : ℕ} (v : Fin (n + 1) → EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => (v j.succ - v 0) i
 def simplexVolume {n : ℕ} :
    (Fin (n + 1) → EuclideanSpace ℝ (Fin n)) → ℝ :=
  fun v => |(simplexEdgeMatrix v).det|
end Analysis
end FunctionalInequalities


