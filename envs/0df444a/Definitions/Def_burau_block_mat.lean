-- Prove2me | Definitions.Def_burau_block_mat
-- name    : burau_block_mat
-- status  : Definition
-- author  : @lt9
-- created : 2026-10-01T01:07:30.386756+00:00
-- url     : https://prove2.me/theorems/26ffa9b0-5e1f-42b7-9787-8178899c9676
-- title:
--   Block matrix machinery: the conjugation P and the embedding 1 (+) A
-- statement:
--   **Block matrix machinery for comparing the two forms of the reduced Burau representation.**
--   Let
--   $$ P=\begin{pmatrix}1&-1&1\\1&-1&0\\1&0&-1\end{pmatrix},\qquad
--      P^{-1}=\begin{pmatrix}1&-1&1\\1&-2&1\\1&-1&0\end{pmatrix} $$
--   (determinant one, `P⁻¹` the adjugate). The node records `P`, `P⁻¹`, the two inverse identities, and the
--   *block embedding* `A ↦ 1 ⊕ A` of a $2\times2$ matrix into the lower-right corner of a $3\times3$ matrix
--   together with its two structural lemmas (`blockMat 1 = 1`, `blockMat (A*B) = blockMat A * blockMat B`,
--   `blockMat A = 1 ↔ A = 1`). These are the linear-algebra inputs for transferring the kernel statement
--   between the $t=-1$ specialization of the unreduced Burau representation (a $3\times3$ representation) and
--   the reduced Burau representation (a $2\times2$ one), i.e. for reducing the milestone frontier
--   `burau_three_spec_kernel_hard` to the kernel statement for the reduced representation.
-- source:
--   Linear algebra behind the t = -1 specialization of the Burau representation; J. S. Birman, *Braids, Links, and Mapping Class Groups*, Ann. of Math. Studies 82 (1974), §3.3.

import Mathlib

set_option autoImplicit false

open Matrix

/-- The conjugating matrix `P = !![1,-1,1; 1,-1,0; 1,0,-1]` (determinant one). -/
def cP : Matrix (Fin 3) (Fin 3) ℤ := !![1, -1, 1; 1, -1, 0; 1, 0, -1]

/-- Its inverse `P⁻¹ = !![1,-1,1; 1,-2,1; 1,-1,0]` (the adjugate, since `det P = 1`). -/
def cPinv : Matrix (Fin 3) (Fin 3) ℤ := !![1, -1, 1; 1, -2, 1; 1, -1, 0]

lemma cP_mul_cPinv : cP * cPinv = 1 := by decide

lemma cPinv_mul_cP : cPinv * cP = 1 := by decide

/-- The block embedding of a `2×2` matrix into the lower-right corner of a `3×3` matrix. -/
def blockMat (A : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0; 0, A 0 0, A 0 1; 0, A 1 0, A 1 1]

lemma blockMat_one : blockMat 1 = 1 := by decide

lemma blockMat_mul (A B : Matrix (Fin 2) (Fin 2) ℤ) :
    blockMat (A * B) = blockMat A * blockMat B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockMat, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three] <;> ring

lemma blockMat_eq_one_iff (A : Matrix (Fin 2) (Fin 2) ℤ) : blockMat A = 1 ↔ A = 1 := by
  constructor
  · intro h
    ext i j
    fin_cases i <;> fin_cases j
    · have h1 := congrFun (congrFun h 1) 1
      simpa [blockMat, Matrix.one_fin_three] using h1
    · have h1 := congrFun (congrFun h 1) 2
      simpa [blockMat, Matrix.one_fin_three] using h1
    · have h1 := congrFun (congrFun h 2) 1
      simpa [blockMat, Matrix.one_fin_three] using h1
    · have h1 := congrFun (congrFun h 2) 2
      simpa [blockMat, Matrix.one_fin_three] using h1
  · intro h
    rw [h, blockMat_one]


