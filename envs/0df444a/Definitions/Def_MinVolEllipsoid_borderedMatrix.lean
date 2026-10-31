-- Prove2me | Definitions.Def_MinVolEllipsoid_borderedMatrix
-- name    : MinVolEllipsoid_borderedMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:43:39.162874+00:00
-- url     : https://prove2.me/theorems/6ba863be-8429-468b-84d1-254e04644f1e
-- title:
--   The bordered block matrix $[F\ c;\ r^\top\ h]$
-- statement:
--   For a $K\times K$ matrix $F$, vectors $c,r\in\mathbb R^K$ and a scalar $h$, the bordered matrix is the $(K+1)\times(K+1)$ matrix
--
--   $$
--   \begin{bmatrix}F & c\\ r^\top & h\end{bmatrix}.
--   $$
--
--   All $(K+1)\times(K+1)$ block matrices of the paper are of this form: the first matrix $[F\ g;\ g^\top\ h-1]$ of (3), the matrix $[X\ x;\ x^\top\ 1]$ of Lemma 4 and (7), the dual matrix $[-A^2\ \ -Ab;\ -b^\top A\ \ \rho-b^\top b]$ of (8), and $[0\ 0;\ 0\ 1]$ of (9).
--
--   **Formalization Note** Rows and columns are indexed by `Fin n ⊕ Unit`, the paper's last row and column being the `Unit` one; the matrix is `Matrix.fromBlocks` with a one-column block $c$ and a one-row block $r^\top$.
-- source:
--   Mittal & Hanasusanto, Finding Minimum Volume Circumscribing Ellipsoids Using Generalized Copositive Programming, arXiv:1807.07507v4, displays (3) p.6, Lemma 4 p.7, (7)–(9) p.8

import Mathlib

open Matrix

namespace MinVolEllipsoid

/-- **The bordered block matrix `[F c; r⊤ h]`** (Mittal & Hanasusanto, arXiv:1807.07507v4, the
`(K+1) × (K+1)` block matrices of (3) p.6, Lemma 4 p.7, (8) and (9) p.8).

`borderedMatrix F c r h` is the `(K+1) × (K+1)` matrix with upper-left block `F` (`K × K`),
last column `c` above `h`, and last row `r⊤` followed by `h`:

`[F c; r⊤ h]`.

The paper's `[F g; g⊤ h − 1]` is `borderedMatrix F g g (h - 1)`, `[X x; x⊤ 1]` is
`borderedMatrix X x x 1`, `[−A² −Ab; −b⊤A ρ − b⊤b]` is
`borderedMatrix (-(A * A)) (-(A *ᵥ b)) (-(b ᵥ* A)) (ρ - b ⬝ᵥ b)` and `[0 0; 0 1]` is
`borderedMatrix 0 0 0 1`.

**Formalization Note** Indices are `Fin n ⊕ Unit`, the paper's last row/column being the `Unit`
one; the matrix is `Matrix.fromBlocks` with a single-column block `c` and a single-row block `r`. -/
def borderedMatrix {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (c r : Fin n → ℝ) (h : ℝ) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ :=
  fromBlocks F (replicateCol Unit c) (replicateRow Unit r) (of fun _ _ => h)

end MinVolEllipsoid


