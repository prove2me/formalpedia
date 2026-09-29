-- Prove2me | Definitions.Def_huangMatrix
-- name    : huangMatrix
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-04-23T04:00:53.738951+00:00
-- url     : https://prove2.me/theorems/40e4861c-9dbb-4ca1-93cb-58e1b7b7e4c0
-- statement:
--   Huang's recursive signed 2^n x 2^n adjacency matrix A_n of the Boolean hypercube, plus three elementary properties proved here: A_n^2 = n*I, A_n is symmetric, and A_n is Hermitian. Depends on the Hypercube definition for index conventions. See Huang, Hao. "Induced subgraphs of hypercubes and a proof of the sensitivity conjecture." Annals of Mathematics 190.3 (2019): 949-955.

import Definitions.Def_Hypercube
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.Tactic.Cases

/-!
# Huang's signed adjacency matrix and its basic properties

This file defines Huang's recursive `2^n × 2^n` signed matrix and proves the
elementary properties shared by every downstream theorem:

- `huangMatrix_sq`          : `A_n^2 = n · I`
- `huangMatrix_is_symm`     : `A_n` is symmetric
- `huangMatrix_is_hermitian`: `A_n` is Hermitian (so it has sorted real eigenvalues)

These are the shared infrastructure needed by the sketch for Theorem 1.1 and by
`Thm_huang_matrix_spectrum_sorted` (Lemma 2.2, whose statement mentions `eigenvalues₀`
and therefore `huangMatrix_is_hermitian`).

The entry-absolute-value characterization `|A_n[u,v]| = 1 if u ~ v else 0` is
promoted to a standalone child at `Theorems/Thm_huangMatrix_entry_abs.lean` —
its case-analytic proof is substantial enough to warrant a separate entity.
-/

/-- Split a boolean function on `Fin (n+1)` into two halves indexed by `Fin n`,
    based on the value of the first coordinate. Used to express the recursive
    block structure of Huang's matrix. -/
def split (n : ℕ) : (Fin (n + 1) → Bool) ≃ (Fin n → Bool) ⊕ (Fin n → Bool) where
  toFun f := if f 0 then Sum.inr (f ∘ Fin.succ) else Sum.inl (f ∘ Fin.succ)
  invFun x := match x with
    | Sum.inl f => Fin.cons false f
    | Sum.inr f => Fin.cons true f
  left_inv f := by
    cases' h : f 0 with h h <;> simp [h]
    · ext i; induction i using Fin.inductionOn <;> simp [h]
    · ext i; induction i using Fin.inductionOn <;> simp [h]
  right_inv x := by cases x <;> aesop

/-- **Huang's signed adjacency matrix** of the n-dimensional hypercube, defined recursively:
    `A₀ = 0`, and `A_{n+1}` is the block matrix `[[Aₙ, I], [I, -Aₙ]]` re-indexed via `split`. -/
noncomputable def huangMatrix : (n : ℕ) → Matrix (Fin n → Bool) (Fin n → Bool) ℝ
  | 0 => 0
  | n + 1 => Matrix.reindex (split n).symm (split n).symm
      (Matrix.fromBlocks (huangMatrix n) 1 1 (-huangMatrix n))

/-- `A_n^2 = n · I`. Key algebraic identity — implies eigenvalues are `±√n`. -/
theorem huangMatrix_sq (n : ℕ) :
    (huangMatrix n) ^ 2 = (n : ℝ) • (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℝ) := by
  induction' n with n ih
  · ext i j; fin_cases i; fin_cases j; simp +decide [huangMatrix]
  · have h_huangMatrix_succ :
        huangMatrix (n + 1) = Matrix.reindex (split n).symm (split n).symm
          (Matrix.fromBlocks (huangMatrix n) 1 1 (-huangMatrix n)) := rfl
    simp_all +decide [sq]
    have h_expand : Matrix.fromBlocks (huangMatrix n) 1 1 (-huangMatrix n) *
        Matrix.fromBlocks (huangMatrix n) 1 1 (-huangMatrix n) =
        Matrix.fromBlocks ((huangMatrix n) * (huangMatrix n) + 1) 0 0
          ((huangMatrix n) * (huangMatrix n) + 1) := by
      simp +decide [Matrix.fromBlocks_multiply]
      rw [add_comm]
    ext i j; simp [split]
    split_ifs <;> simp +decide [*, Matrix.one_apply]
    · split_ifs <;> simp_all +decide [funext_iff, Fin.forall_fin_succ]
    · aesop
    · grind
    · split_ifs <;> simp_all +decide [funext_iff, Fin.forall_fin_succ]

/-- `A_n` is symmetric. -/
theorem huangMatrix_is_symm (n : ℕ) : (huangMatrix n).IsSymm := by
  induction' n with n ih <;> simp_all +decide [huangMatrix]
  simp_all +decide [Matrix.IsSymm, Matrix.fromBlocks_transpose]

/-- `A_n` is Hermitian (real-symmetric ⇒ Hermitian), so it has sorted real eigenvalues. -/
theorem huangMatrix_is_hermitian (n : ℕ) : (huangMatrix n).IsHermitian :=
  huangMatrix_is_symm n


