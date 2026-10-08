-- Prove2me | Definitions.Def_ProjLikeRetr_Stiefel_stiefel
-- name    : ProjLikeRetr_Stiefel_stiefel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T15:11:19.540879+00:00
-- url     : https://prove2.me/theorems/757de601-b8ae-4c9e-a752-f0732b513ada
-- title:
--   §3.3, p. 10 — the Stiefel manifold V_{n,m} = {X ∈ ℝ^{n×m} : XᵀX = I_m}
-- statement:
--   For natural numbers $m \le n$, the **Stiefel manifold** of orthonormal $m$-frames in $\mathbb R^n$ is the set of real $n\times m$ matrices with orthonormal columns,
--
--   $$V_{n,m}=\{X\in\mathbb R^{n\times m}:\ X^\top X=I_m\}.$$
--
--   For $m=n$ it is the group $\mathbf O_n$ of orthogonal matrices of size $n$. It is the submanifold onto which Proposition 3.4 of the paper projects.
--
--   **Formalization Note** `stiefel n m` is the set of `X : Matrix (Fin n) (Fin m) ℝ` with `Xᵀ * X = 1`. The page's standing assumption $m\le n$ is a hypothesis of each theorem that uses the set, not part of the definition (for $m>n$ the set is empty).
-- source:
--   Absil & Malick, Projection-like retractions on matrix manifolds, HAL hal-00651608v2, p. 10, §3.3 (definition of V_{n,m})

import Mathlib

open scoped Matrix

namespace ProjLikeRetr.Stiefel

/-- §3.3, p. 10: the Stiefel manifold `V_{n,m} = {X ∈ ℝ^{n×m} : XᵀX = I_m}` of orthonormal
`m`-frames in `ℝⁿ`, as a set of real `n × m` matrices. The page assumes `m ≤ n`; every theorem of
the mission carries that hypothesis (for `m > n` the set is empty). For `n = m` it is the group
`Matrix.orthogonalGroup (Fin n) ℝ` of orthogonal matrices. -/
def stiefel (n m : ℕ) : Set (Matrix (Fin n) (Fin m) ℝ) :=
  {X | Xᵀ * X = 1}

end ProjLikeRetr.Stiefel


