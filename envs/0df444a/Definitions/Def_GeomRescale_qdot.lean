-- Prove2me | Definitions.Def_GeomRescale_qdot
-- name    : GeomRescale_qdot
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:13:47.728099+00:00
-- url     : https://prove2.me/theorems/225d4103-f4e3-405d-8fa9-31191d0530d2
-- title:
--   The scalar product $\langle x, y \rangle_Q$
-- statement:
--   For a matrix $Q$ and vectors $x, y \in \mathbb{R}^V$,
--
--   $$\langle x, y \rangle_Q = x^{\mathsf T} Q y.$$
--
--   For symmetric positive definite $Q$ this is a scalar product. Algorithm 1 runs in this geometry.
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, §2, p.3

import Mathlib

namespace GeomRescale

/-- The scalar product `⟨x, y⟩_Q = xᵀQy` (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, §2, p.3). -/
def qdot {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ) : ℝ :=
  x ⬝ᵥ (Q.mulVec y)

end GeomRescale


