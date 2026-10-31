-- Prove2me | Definitions.Def_MinVolEllipsoid_ineq3Right
-- name    : MinVolEllipsoid_ineq3Right
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:44:30.52348+00:00
-- url     : https://prove2.me/theorems/617a877e-9d6a-448e-9497-65d7b7d67db2
-- title:
--   The matrix $[F\ g\ A;\ g^\top\ h\ b^\top;\ A\ b\ \mathbb I]$ of (3)
-- statement:
--   For $A\in\mathbb R^{K\times K}$, $b,g\in\mathbb R^K$, $F\in\mathbb R^{K\times K}$ and $h\in\mathbb R$, the second matrix of display (3) is the $(2K+1)\times(2K+1)$ matrix
--
--   $$
--   \begin{bmatrix}F & g & A\\ g^\top & h & b^\top\\ A & b & \mathbb I\end{bmatrix}.
--   $$
--
--   Theorem 1 requires it to be positive semidefinite. For symmetric $F$ and $A$ it is symmetric; by a Schur complement it is positive semidefinite exactly when $[F\ g;\ g^\top\ h]\succeq[A\ b]^\top[A\ b]$, which is how (3) linearizes the quadratic dependence of (9) on $(A,b)$.
--
--   **Formalization Note** The matrix is a $2\times2$ block matrix over the index type `(Fin n ⊕ Unit) ⊕ Fin n` (first the $K$ indices, then the paper's middle scalar index `Unit`, then the last $K$ indices), with upper-left block $[F\ g;\ g^\top\ h]$, upper-right block $[A;\ b^\top]$, lower-left block $[A\ b]$ and lower-right block the identity. The page's layout is copied literally, without transposing $A$.
-- source:
--   Mittal & Hanasusanto, Finding Minimum Volume Circumscribing Ellipsoids Using Generalized Copositive Programming, arXiv:1807.07507v4, Theorem 1, display (3), p.6

import Mathlib
import Definitions.Def_MinVolEllipsoid_borderedMatrix
import Definitions.Def_MinVolEllipsoid_stackAb

open Matrix

namespace MinVolEllipsoid

/-- **The `(2K+1) × (2K+1)` matrix of the second inequality of (3)** (Mittal & Hanasusanto,
arXiv:1807.07507v4, Theorem 1, display (3), p.6):

`[F g A; g⊤ h b⊤; A b 𝕀]`.

Written as a `2 × 2` block matrix over the index split `(K+1) + K`: the upper-left block is
`[F g; g⊤ h]`, the upper-right block is `[A; b⊤]` (the matrix `A` above the row `b⊤`), the
lower-left block is `[A b]`, and the lower-right block is the identity `𝕀`.

**Formalization Note** Indices are `(Fin n ⊕ Unit) ⊕ Fin n`: the first `K` indices, then the
paper's middle (scalar) index `Unit`, then the last `K` indices. The page's layout is copied
literally (entry `(k, j)` of the upper-right block is `A k j`, entry `(j, k)` of the lower-left
block is `A j k`); for symmetric `A` the whole matrix is symmetric. -/
def ineq3Right {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (F : Matrix (Fin n) (Fin n) ℝ) (g : Fin n → ℝ) (h : ℝ) :
    Matrix ((Fin n ⊕ Unit) ⊕ Fin n) ((Fin n ⊕ Unit) ⊕ Fin n) ℝ :=
  fromBlocks (borderedMatrix F g g h)
    (Matrix.of fun i j => Sum.elim (fun k => A k j) (fun _ => b j) i)
    (stackAb A b) 1

end MinVolEllipsoid


