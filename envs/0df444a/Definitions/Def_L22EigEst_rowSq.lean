-- Prove2me | Definitions.Def_L22EigEst_rowSq
-- name    : L22EigEst_rowSq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:11:37.376486+00:00
-- url     : https://prove2.me/theorems/3fc3dd97-7ce7-44c2-b5a5-6f3f80727491
-- title:
--   Squared row norms $\|A_i\|_2^2$ and the Frobenius norm $\|A\|_F$
-- statement:
--   For a real matrix $A$ with finitely many rows and columns, the **squared norm of row $i$** and the **squared Frobenius norm** are
--
--   $$\|A_i\|_2^2=\sum_j A_{ij}^2,\qquad \|A\|_F^2=\sum_{i}\sum_j A_{ij}^2,$$
--
--   and the **Frobenius norm** is $\|A\|_F=\sqrt{\|A\|_F^2}$.
--
--   In the $\ell_2^2$-sampling model the algorithm is given the list $\|A_1\|_2^2,\dots,\|A_n\|_2^2$ of a symmetric $A\in\mathbb R^{n\times n}$; their sum is $\|A\|_F^2$, and every error bound of the paper is a multiple of $\varepsilon\|A\|_F$.
--
--   **Formalization Note** The row and column index types are arbitrary finite types, so the same definitions apply to $n\times n$ matrices indexed by `Fin n` and to the $sn\times sn$ matrix $VAV^\top$ of Algorithm 2, indexed by `Fin s × Fin n`.
-- source:
--   Menand, Waingarten, Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation, STOC 2027 submission (manuscript sha256 b1f6adce…), §1, p.3 (ℓ₂²-sampling model) and Theorem 4, p.10

import Mathlib

namespace L22EigEst

/-- **Squared row norm** `‖A_i‖₂² = ∑_j A_{ij}²` of row `i` of a real matrix.
Menand, Waingarten, *Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation*, STOC 2027
submission (manuscript sha256 b1f6adce…), §1, p.3 and Theorem 4, p.10: the algorithm receives
"the squared row norms ∥A1∥2², …, ∥An∥2² of A".

**Formalization Note.** Stated for any finite row and column index types, so that it applies both
to `n × n` matrices indexed by `Fin n` and to the `sn × sn` matrix `VAV⊺` of Algorithm 2, which is
indexed by `Fin s × Fin n`. -/
def rowSq {m k : Type*} [Fintype k] (A : Matrix m k ℝ) (i : m) : ℝ :=
  ∑ j, A i j ^ 2

/-- **Squared Frobenius norm** `‖A‖_F² = ∑_{i,j} A_{ij}²`. Menand, Waingarten, STOC 2027 submission
(manuscript sha256 b1f6adce…), used throughout, e.g. Theorem 4, p.10, and Definition 3.1, p.10. -/
def frobSq {m k : Type*} [Fintype m] [Fintype k] (A : Matrix m k ℝ) : ℝ :=
  ∑ i, ∑ j, A i j ^ 2

/-- **Frobenius norm** `‖A‖_F = √(∑_{i,j} A_{ij}²)`. Menand, Waingarten, STOC 2027 submission
(manuscript sha256 b1f6adce…), Theorem 4, p.10 (the error bound `ε‖A‖_F`). -/
noncomputable def frob {m k : Type*} [Fintype m] [Fintype k] (A : Matrix m k ℝ) : ℝ :=
  Real.sqrt (frobSq A)

end L22EigEst


