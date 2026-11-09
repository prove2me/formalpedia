-- Prove2me | Definitions.Def_L22EigEst_zeroed
-- name    : L22EigEst_zeroed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:15:41.361966+00:00
-- url     : https://prove2.me/theorems/94aa35e1-f26d-45c7-a499-b43048684116
-- title:
--   The zeroed matrix $A'$ of equation (2)
-- statement:
--   For a symmetric $A\in\mathbb R^{n\times n}$ and $\varepsilon>0$, the matrix $A'$ of equation (2) is
--
--   $$A'_{ij}=\begin{cases}0 & i=j \text{ and } \|A_i\|_2^2\le \frac{\varepsilon^2}{4}\|A\|_F^2,\\[2pt] 0 & i\ne j \text{ and } \dfrac{\|A_i\|_2^2\|A_j\|_2^2}{\|A\|_F^2}\le\frac{\varepsilon^2}{4}|A_{ij}|^2,\\[2pt] A_{ij} & \text{otherwise.}\end{cases}$$
--
--   It zeroes the entries that are large relative to the norms of their row and column. Algorithm 1 forms $A'$ implicitly from the queried entries and the given row norms. Lemma 4.1 shows that this moves every eigenvalue by at most $\varepsilon\|A\|_F$.
--
--   **Formalization Note** The off-diagonal test is stated multiplied out, $\|A_i\|_2^2\|A_j\|_2^2\le\frac{\varepsilon^2}{4}|A_{ij}|^2\|A\|_F^2$, equivalent for $A\ne0$ (at $A=0$ every entry is $0$ either way). The module proves that $A'$ is symmetric.
-- source:
--   Menand, Waingarten, Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation, STOC 2027 submission (manuscript sha256 b1f6adce…), Algorithm 1 (Figure 1), p.11, eq. (2)

import Definitions.Def_L22EigEst_rowSq

namespace L22EigEst

/-- **The zeroed matrix `A′` of equation (2)** (Algorithm 1, Figure 1, p.11), Menand, Waingarten,
STOC 2027 submission (manuscript sha256 b1f6adce…):
`A′_ij = 0` if `i = j` and `‖A_i‖₂² ≤ (ε²/4)‖A‖_F²`; `0` if `i ≠ j` and
`‖A_i‖₂²‖A_j‖₂²/‖A‖_F² ≤ (ε²/4)|A_ij|²`; `A_ij` otherwise.

**Formalization Note.** The off-diagonal test is stated multiplied out,
`‖A_i‖₂²‖A_j‖₂² ≤ (ε²/4)|A_ij|²‖A‖_F²`, which is equivalent for `A ≠ 0`; at `A = 0` every entry is
`0` under either reading. Indices are 0-based. -/
noncomputable def zeroed {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    if i = j then (if rowSq A i ≤ ε ^ 2 / 4 * frobSq A then 0 else A i j)
    else (if rowSq A i * rowSq A j ≤ ε ^ 2 / 4 * A i j ^ 2 * frobSq A then 0 else A i j)

/-- `A′` is symmetric when `A` is (Algorithm 1, p.11: "the symmetric matrix A′"). -/
theorem zeroed_isHermitian {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (ε : ℝ) : (zeroed A ε).IsHermitian := by
  ext i j
  have h : A j i = A i j := by
    have := congrFun (congrFun hA i) j
    simpa [Matrix.conjTranspose_apply] using this
  simp only [Matrix.conjTranspose_apply, star_trivial, zeroed]
  by_cases hij : i = j
  · subst hij; simp
  · have hji : ¬ j = i := fun e => hij e.symm
    simp only [hij, hji, if_false, h, mul_comm (rowSq A j) (rowSq A i)]

end L22EigEst


