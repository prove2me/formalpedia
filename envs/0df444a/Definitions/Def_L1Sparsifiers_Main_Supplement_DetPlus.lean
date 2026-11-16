-- Prove2me | Definitions.Def_L1Sparsifiers_Main_Supplement_DetPlus
-- name    : L1Sparsifiers_Main_Supplement_DetPlus
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T12:15:22.22187+00:00
-- url     : https://prove2.me/theorems/2f1777e5-ecc1-4c24-a6be-b488060198f4
-- title:
--   The positive-part determinant $\det_+$ of a symmetric matrix
-- statement:
--   For a symmetric matrix $B\in\mathbb R^{n\times n}$ the **positive-part determinant** is
--   $$\det\nolimits_+(B)=\begin{cases}\det(B)&\text{if }B\succeq0,\\0&\text{otherwise,}\end{cases}$$
--   where $B\succeq0$ means that $B$ is positive semidefinite. It is always nonnegative. For $n=0$ the empty matrix is positive semidefinite and $\det_+$ equals $1$.
--
--   It is the spectral analogue of the volume $t\mapsto\mathrm{Vol}_n(K\ominus Z_t)$: the function $t\mapsto\det_+(B-\sum_i t_iA_i)$ plays the role of the left-over volume in the proof of the spectral positivity bound (Lemma 27, Theorem 29).
--
--   **Formalization Note** $B\succeq0$ is `Matrix.PosSemidef` over $\mathbb R$, which includes symmetry, so a non-symmetric argument gets the value $0$; the source applies $\det_+$ to symmetric matrices only.
-- source:
--   Victor Reis, Thomas Rothvoss, Linear-size ℓ1 sparsifiers, STOC 2027 submission #162 (October 2026; PDF SHA-256 5137e7dee3cd303bd508f90f5f42c955632af5dc2ec978d9ef575bae4ce23710), §7, definition of det₊, p.18

import Mathlib

namespace L1Sparsifiers.Main.Supplement

/-- **Positive-part determinant** `det₊` (Reis–Rothvoss, *Linear-size ℓ1 sparsifiers*, STOC 2027
submission #162, §7, p.18): for a symmetric `B ∈ ℝ^{n×n}`,
`det₊(B) = det(B)` if `B ⪰ 0`, and `det₊(B) = 0` otherwise.

`B ⪰ 0` is `Matrix.PosSemidef` over `ℝ`, which includes symmetry; the source defines `det₊` only for
symmetric matrices, and every argument used below is symmetric. For `n = 0` the empty matrix is
positive semidefinite with determinant `1`. -/
noncomputable def detPlus {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) : ℝ := by
  classical
  exact if B.PosSemidef then B.det else 0

end L1Sparsifiers.Main.Supplement


