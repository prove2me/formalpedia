-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Normalization
-- name    : KLS408915f_FunctionalInequalities_Analysis_Convex_Normalization
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T12:52:03.104063+00:00
-- url     : https://prove2.me/theorems/65e663ac-ef9b-4dba-81e0-7ef758bd80be
-- title:
--   Simplex edge matrix and volume
-- statement:
--   For vertices $v_0,\ldots,v_n\in\mathbb{R}^n$, `simplexEdgeMatrix v` is the matrix whose column $j$ is $v_{j+1}-v_0$, and `simplexVolume v` is the absolute value of its determinant. The module supplies auxiliary facts about maximal-volume simplices, simplex coordinates, and inclusions between standard simplices, balls, and boxes.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Normalization.lean#L20-L27 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Normalization`, definition bundle `KLS408915f_FunctionalInequalities_Analysis_Convex_Normalization`; the repository is private at upload time).

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


