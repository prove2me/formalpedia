-- Prove2me | Definitions.Def_GeomRescale_IsMinNormPoint
-- name    : GeomRescale_IsMinNormPoint
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:14:33.529985+00:00
-- url     : https://prove2.me/theorems/a43519c9-fe9a-4dd3-ac91-fe93ee3e4c30
-- title:
--   An optimal solution of the minimum-norm point problem (6)
-- statement:
--   The point $z$ is an optimal solution of
--
--   $$\min\Bigl\{\tfrac12 \|x\|_2^2 : x \in B(f)\Bigr\}.$$
--
--   Fujishige's theorem (Theorem 2.3) reduces submodular function minimization to this problem.
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, display (6), p.5

import Mathlib
import Definitions.Def_SchrijverSFM_Alg_Setting
import Definitions.Def_GeomRescale_norm2

namespace GeomRescale

/-- `z` is an optimal solution of `min {½‖x‖₂² : x ∈ B(f)}` (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, display (6), p.5). -/
def IsMinNormPoint {n : ℕ} (f : Finset (Fin n) → ℝ) (z : Fin n → ℝ) : Prop :=
  z ∈ SchrijverSFM.Alg.baseB f ∧
    ∀ x ∈ SchrijverSFM.Alg.baseB f, (1 / 2 : ℝ) * norm2 z ^ 2 ≤ (1 / 2 : ℝ) * norm2 x ^ 2

end GeomRescale


