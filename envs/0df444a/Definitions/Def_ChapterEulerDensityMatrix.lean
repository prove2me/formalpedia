-- Prove2me | Definitions.Def_ChapterEulerDensityMatrix
-- name    : ChapterEulerDensityMatrix
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T03:52:29.589577+00:00
-- url     : https://prove2.me/theorems/88b53ed8-7c0a-4990-99fa-fab7597c69cd
-- title:
--   Chapter EulerDensityMatrix
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterEulerDensityMatrix.lean`): generated def bundle for ChapterEulerDensityMatrix. See BookProof/ChapterEulerDensityMatrix.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterEulerDensityMatrix.lean

import Mathlib


/-!
# Chapter — Euler's formula for the 2-state density matrix

Formalization of the *density-matrix* identity in `book.tex`, chapter
*"Wave-function collapse versus Euler's formula"*, §*"Euler's formula for the
probability clock"* (`book.tex` line ~3300).  For the 2-state probability clock
with wave function `Ψ(t) = (cos t, sin t)`, the book writes the density matrix
`Ψ Ψ†` as a *multi-dimensional Euler's formula*:

> `Ψ Ψ† = [[cos²t, cos t sin t], [cos t sin t, sin²t]]`
>        `= ½·I + [[½,0],[0,-½]]·(cos 2t + J sin 2t)`,
>   where `J = [[0,1],[-1,0]]` plays the role of the imaginary unit,

and the *collapse* of the wave function is "setting the off-diagonal part
(i.e. the part proportional to `J`) of the original density matrix to zero",
producing the classical probability distribution on the diagonal
`[[cos²t,0],[0,sin²t]]`.

This module complements `BookProof.ChapterE` (which proves the *collapsed*
diagonal identity `collapse_density`) by formalizing the *full pre-collapse
density matrix* in Euler form, the fact that `J² = -1`, and the standard
density-matrix properties (unit trace, symmetry, and purity/idempotency).

All results are `sorry`-free and `axiom`-clean (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped Matrix

namespace BookProof.ChapterEulerDensityMatrix

/-- The 2-state clock wave function `Ψ(t) = (cos t, sin t)`. -/
noncomputable def clockPsi (t : ℝ) : Fin 2 → ℝ := ![Real.cos t, Real.sin t]

/-- The density matrix `ρ(t) = Ψ Ψᵀ` (the outer product of the wave function
with itself). -/
noncomputable def densityMatrix (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.vecMulVec (clockPsi t) (clockPsi t)

/-- The matrix `J = [[0,1],[-1,0]]` that plays the role of the imaginary unit
in Euler's formula for the density matrix. -/
def Jdens : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

/-- The diagonal generator `Z = [[½,0],[0,-½]]`. -/
noncomputable def Zdiag : Matrix (Fin 2) (Fin 2) ℝ := !![1 / 2, 0; 0, -1 / 2]























end BookProof.ChapterEulerDensityMatrix


