-- Prove2me | Definitions.Def_MagicSquaresTransforms
-- name    : MagicSquaresTransforms
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-09-16T14:39:16.914375+00:00
-- url     : https://prove2.me/theorems/667c7c46-2268-4c23-9bda-5a2fc62d941d
-- title:
--   Magic squares: symmetries and affine transformations
-- statement:
--   This module extends `Definitions.Def_MagicSquares` with the elementary transformations used in the structural theory of magic squares: the transpose of a square, the vertical and horizontal flips, and the affine substitution $M \\mapsto aM+b$ applied entrywise.
--
--   For the affine map it records the exact effect on every line sum:
--   row sums, column sums, the main diagonal, and the anti-diagonal all become
--   $aS+nb$ when the original line sum is $S$.
--
--   The remaining invariance facts (flips and transpose preserve semi-magic, magic, and panmagic status) are deliberately left as ordinary theorems to be proved from the definitions.
-- source:
--   Beck, Cohen, Cuomo & Gribelyuk, The number of ``magic'' squares, cubes and hypercubes, Amer. Math. Monthly 110 (2003), 707--717; standard definitions of symmetry operations on $n \times n$ arrays.

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_MagicSquares

set_option autoImplicit false

/-! # Magic-square symmetries and elementary transformations

This module extends `Definitions.Def_MagicSquares` with the standard symmetries
(transpose, vertical/horizontal flips) and affine substitutions used in the
structural theory of magic squares.

Only the operations themselves and the explicit affine line-sum identities are
provided; permutation invariance of sums is used directly in theorem proofs.
-/

namespace MagicSquares

variable {n : ℕ} {α : Type*}

/-! ## Symmetries of the square -/

/-- The transpose of a square. -/
def transpose [AddCommMonoid α] (M : Square n α) : Square n α :=
  fun i j => M j i

/-- Vertical flip: reverse the order of the rows. -/
def flipVertical (M : Square n α) : Square n α :=
  fun i j => M (Fin.rev i) j

/-- Horizontal flip: reverse the order of the columns. -/
def flipHorizontal (M : Square n α) : Square n α :=
  fun i j => M i (Fin.rev j)

/-! ## Affine substitution -/

/-- The affine transformation `M ↦ a • M + b` (entrywise). -/
def affine [Semiring α] (a b : α) (M : Square n α) : Square n α :=
  fun i j => a * M i j + b

variable [Semiring α]

private lemma sum_const_fin (b : α) :
    ∑ _j : Fin n, b = n • b := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  all_goals simp

@[simp]
lemma rowSum_affine (M : Square n α) (a b : α) (i : Fin n) :
    rowSum (affine a b M) i = a * rowSum M i + n • b := by
  simp [rowSum, affine, Finset.mul_sum, Finset.sum_add_distrib, sum_const_fin]

@[simp]
lemma colSum_affine (M : Square n α) (a b : α) (j : Fin n) :
    colSum (affine a b M) j = a * colSum M j + n • b := by
  simp [colSum, affine, Finset.mul_sum, Finset.sum_add_distrib, sum_const_fin]

@[simp]
lemma diagSum_affine (M : Square n α) (a b : α) :
    diagSum (affine a b M) = a * diagSum M + n • b := by
  simp [diagSum, affine, Finset.mul_sum, Finset.sum_add_distrib, sum_const_fin]

@[simp]
lemma antiDiagSum_affine (M : Square n α) (a b : α) :
    antiDiagSum (affine a b M) = a * antiDiagSum M + n • b := by
  simp [antiDiagSum, affine, Finset.mul_sum, Finset.sum_add_distrib, sum_const_fin]

end MagicSquares


