-- Prove2me | Definitions.Def_ChapterDoubleSlit
-- name    : ChapterDoubleSlit
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T22:37:17.891847+00:00
-- url     : https://prove2.me/theorems/c3be2472-0ded-4efc-b561-b03641e118fa
-- title:
--   Source: `book.tex`, chapter *"Reconstructing the classical trajectory of any isolated quantum system"*, §*"The Young's d ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.DoubleSlit`, source chapter `BookProof/ChapterDoubleSlit.lean`).
--
--   Source: `book.tex`, chapter *"Reconstructing the classical trajectory of any isolated quantum system"*, §*"The Young's double slit experiment"* (`book.tex` line ~3082).
--
--   The book models the two-slit experiment for a two-state (two-angle) electron by the normalized `2×2` Hadamard matrix
--
--   `H = (1/√2) · [[1, 1], [1, -1]]`,
--
--   with initial wave-function `Ψ = (1, 0)` fired at the source `(S1)`.
--
--   * If the second slit is **closed**, the evolution `(S1) → (S2)` is the identity and the evolution `(S2) → (F)` is `H`, so the final state is `H·Ψ = (1/√2)(1,1)` giving the **uniform** Born distribution `(1/2, 1/2)` (the electron arrives along angle 1 or angle 2 with equal probability). * If the second slit is **open**, the evolution `(S1) → (S2)` is `H` (the electron goes through both slits with equal probability) and `(S2) → (F)` is again `H`, so the final state is `H·(H·Ψ) = H²·Ψ = Ψ = (1, 0)` giving the **certain** Born distribution `(1, 0)` (the electron arrives only along angle 1).
--
--   The whole "mystery" of self-interference (`50/50` at the intermediate step becoming `100/0` at the detector) is the purely algebraic fact that the Hadamard matrix is an **involution**, `H² = 1`: composing the two non-deterministic symmetry transformations produces certainty, which is *not* what a stochastic process applying the two steps in sequence would give.
--
--   This file makes that self-contained content precise. We reuse only the concrete Hadamard matrix (as in `ChapterE.lean`); nothing here touches the gravity or the γ/Majorana lines.
--
--   Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`).
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterDoubleSlit.lean

import Mathlib
import Mathlib

import Mathlib

import Mathlib

/-!
# Chapter "Reconstructing the classical trajectory of any isolated quantum system"
— the Young's double-slit experiment as an involutive unitary

Source: `book.tex`, chapter *"Reconstructing the classical trajectory of any
isolated quantum system"*, §*"The Young's double slit experiment"*
(`book.tex` line ~3082).

The book models the two-slit experiment for a two-state (two-angle) electron by
the normalized `2×2` Hadamard matrix

  `H = (1/√2) · [[1, 1], [1, -1]]`,

with initial wave-function `Ψ = (1, 0)` fired at the source `(S1)`.

* If the second slit is **closed**, the evolution `(S1) → (S2)` is the identity
  and the evolution `(S2) → (F)` is `H`, so the final state is `H·Ψ = (1/√2)(1,1)`
  giving the **uniform** Born distribution `(1/2, 1/2)` (the electron arrives
  along angle 1 or angle 2 with equal probability).
* If the second slit is **open**, the evolution `(S1) → (S2)` is `H` (the electron
  goes through both slits with equal probability) and `(S2) → (F)` is again `H`,
  so the final state is `H·(H·Ψ) = H²·Ψ = Ψ = (1, 0)` giving the **certain**
  Born distribution `(1, 0)` (the electron arrives only along angle 1).

The whole "mystery" of self-interference (`50/50` at the intermediate step
becoming `100/0` at the detector) is the purely algebraic fact that the Hadamard
matrix is an **involution**, `H² = 1`: composing the two non-deterministic
symmetry transformations produces certainty, which is *not* what a stochastic
process applying the two steps in sequence would give.

This file makes that self-contained content precise.  We reuse only the concrete
Hadamard matrix (as in `ChapterE.lean`); nothing here touches the gravity or the
γ/Majorana lines.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

open Matrix
open scoped BigOperators

namespace BookProof.ChapterDoubleSlit

/-- The normalized `2×2` Hadamard matrix — the double-slit time evolution. -/
noncomputable def H : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / Real.sqrt 2 : ℂ) • !![1, 1; 1, -1]

/-- The initial wave-function `Ψ = (1, 0)` fired at the source `(S1)`. -/
def psi0 : Fin 2 → ℂ := ![1, 0]

/-- The Born probability of component `i` of a wave-function `ψ`. -/
noncomputable def bornProb (ψ : Fin 2 → ℂ) (i : Fin 2) : ℝ := ‖ψ i‖ ^ 2













end BookProof.ChapterDoubleSlit


