-- Prove2me | Definitions.Def_ChapterAbelianDiagonal
-- name    : ChapterAbelianDiagonal
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T03:17:54.829051+00:00
-- url     : https://prove2.me/theorems/04d7580b-c269-4d7c-88b1-bc9d24d456bb
-- title:
--   Chapter AbelianDiagonal
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterAbelianDiagonal.lean`): generated def bundle for ChapterAbelianDiagonal. See BookProof/ChapterAbelianDiagonal.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterAbelianDiagonal.lean

import Mathlib


/-!
# The finite (type `I_n`) case of the abelian von Neumann classification

`BookProof/ChapterSelectingEvents.lean` (book Chapter 13, `book.tex` ~8789–8800)
records von Neumann's classification of abelian von Neumann algebras: every one
of them is `*`-isomorphic to one of

`ℓ∞({1,…,n})`, `ℓ∞(ℕ)`, `L∞([0,1])`, `L∞([0,1] ∪ {1,…,n})`, `L∞([0,1] ∪ ℕ)`.

The full five-way classification is a deep theorem and is *not* claimed here.
What **is** proved in this file is its first case, in the concrete
finite-dimensional model `Mat(n, ℂ)`:

* `diagonalStarAlgHom` — the `*`-algebra embedding `ℓ∞({1,…,n}) = (n → ℂ) →
  Mat(n, ℂ)` given by `d ↦ diag(d)`, and `diagonalStarAlgHom_injective`;
* `diagonal_commute` — its image is abelian;
* `commutant_diagonal_eq_diagonal` — its image is **maximal** abelian: anything
  commuting with all diagonal matrices is itself diagonal;
* `vonNeumann_abelian_typeI_case` — the headline packaging: `ℓ∞({1,…,n})` is
  realized inside `Mat(n, ℂ)` as a maximal abelian self-adjoint subalgebra.

All results are `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

namespace BookProof.AbelianDiagonal

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The `*`-algebra embedding of `ℓ∞({1,…,n}) = (n → ℂ)` into `Mat(n, ℂ)`,
`d ↦ diag(d)`. -/
noncomputable def diagonalStarAlgHom : (n → ℂ) →⋆ₐ[ℂ] Matrix n n ℂ where
  toFun d := Matrix.diagonal d
  map_one' := Matrix.diagonal_one
  map_mul' d e := (Matrix.diagonal_mul_diagonal d e).symm
  map_zero' := Matrix.diagonal_zero
  map_add' d e := (Matrix.diagonal_add d e).symm
  commutes' r := by
    ext i j
    by_cases h : i = j <;> simp [h, Algebra.algebraMap_eq_smul_one]
  map_star' d := by
    simp [Matrix.star_eq_conjTranspose]













end BookProof.AbelianDiagonal


