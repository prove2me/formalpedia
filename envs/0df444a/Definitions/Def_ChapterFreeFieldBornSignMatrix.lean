-- Prove2me | Definitions.Def_ChapterFreeFieldBornSignMatrix
-- name    : ChapterFreeFieldBornSignMatrix
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-05T03:30:16.0702+00:00
-- url     : https://prove2.me/theorems/5bb373ea-6d39-4af7-92c5-c81d339f25c7
-- title:
--   ChapterFreeFieldBornSignMatrix

import Definitions.Def_ChapterFreeFieldBornSignHom
import Definitions.Def_ChapterFreeFieldBornSignAction
import Mathlib


/-!
# Chapter "Wave-function parametrization of a probability measure", §5 —
# matrix representation of the diagonal sign gauge

This file packages the boolean sign action from
`ChapterFreeFieldBornSignAction` as diagonal real matrices.  The resulting
matrix representation acts on coordinate vectors exactly as `boolFlip`, is
orthogonal, respects coordinate-wise `xor`, and has determinant equal to the
parity character `(-1) ^ flipCount b` computed in
`ChapterFreeFieldBornSignHom`.

## Main results

* `flipMatrix_mulVec` — the diagonal matrix acts as `boolFlip`.
* `flipMatrix_xor` — coordinate-wise `xor` becomes matrix multiplication.
* `flipMatrix_sq` — every sign matrix is an involution.
* `flipMatrix_transpose_mul` — every sign matrix is orthogonal.
* `det_flipMatrix` — its determinant is `(-1) ^ flipCount b`.
-/

open BookProof.ChapterFreeFieldBornSignAction
open BookProof.ChapterFreeFieldBornSignHom

namespace BookProof.ChapterFreeFieldBornSignMatrix

variable {n : ℕ}

/-- The diagonal matrix representing a boolean sign choice. -/
def flipMatrix (b : Fin n → Bool) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (flipVec b)

/-
The diagonal sign matrix acts on coordinate vectors exactly as `boolFlip`.
-/


/-
The all-false choice is represented by the identity matrix.
-/


/-
Coordinate-wise `xor` is represented by matrix multiplication.
-/


/-
Every sign matrix squares to the identity.
-/


/-
Every sign matrix is orthogonal.
-/


/-
The determinant of the sign matrix is its parity character.
-/


end BookProof.ChapterFreeFieldBornSignMatrix


