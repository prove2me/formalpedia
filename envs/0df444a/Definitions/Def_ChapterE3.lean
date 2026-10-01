-- Prove2me | Definitions.Def_ChapterE3
-- name    : ChapterE3
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T03:47:41.883324+00:00
-- url     : https://prove2.me/theorems/106983cc-2801-4500-a09b-65452bd2432b
-- title:
--   Chapter E3
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterE3.lean`): generated def bundle for ChapterE3. See BookProof/ChapterE3.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterE3.lean

import Mathlib


/-!
# Chapter E (continued) — Euler's formula for the density matrix

This file formalizes the **density-matrix ("Euler's formula for the corresponding
density matrices")** content of the `book.tex` section *"Euler's formula for a
phase-space with 4 states"* (Chapter *"Wave-function collapse versus Euler's
formula"*, `book.tex` line ~3478), complementing:

* `BookProof/ChapterE.lean` — the 2-state probability clock and the scalar
  `cos²`/rotation core, and
* `BookProof/ChapterE2.lean` — the stick-breaking *Born probabilities*
  `P(n) = (∏ s²)·c²`.

The book writes each collapse step of a real normalized wave-function
`φ = cos θ · l + sin θ · w` (with `l` the "measured" basis vector and `w` the
"remaining" wave-function) as an **Euler's formula for the rank-1 density matrix**
`φφ†`:

```
φφ† = ½(l l† + w w†) + ½ cos(2θ) (l l† − w w†) + ½ sin(2θ) (l w† + w l†)
```

with `J := l w† − w l†` playing the role of the *imaginary unit* in the
2-dimensional subspace `span{l, w}`.  "Collapse = taking the real part" is then
the statement that the diagonal (the classical conditional probability) is the
`cos(2θ)` part, giving `P(l | l or above) = ½ + ½ cos(2θ) = cos²θ`.

We model column vectors as `l w : Fin n → ℝ` and their outer products
`l l†` as `Matrix.vecMulVec l l`.

Deliverables:

* `euler_density_matrix` — **headline**: the density-matrix Euler formula, an
  algebraic identity requiring **no** orthonormality;
* `eulerJ_antisymm` — the "imaginary unit" `J = l w† − w l†` is antisymmetric
  (`Jᵀ = −J`);
* `eulerJ_sq` — under orthonormality `J² = −(l l† + w w†)`, i.e. `J` squares to
  minus the identity of the subspace: it genuinely behaves like `i`;
* `euler_density_diag_real` — "taking the real part": the `l`-diagonal entry of
  `φφ†` is `cos²θ = ½ + ½ cos(2θ)`, the book's conditional probability;
* `euler_density_isIdempotent` — under orthonormality `φφ†` is a genuine rank-1
  projector (`φφ† · φφ† = φφ†`), the density matrix of a pure state.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

open scoped Matrix BigOperators

namespace BookProof.ChapterE3

variable {n : ℕ}

/-- The "imaginary unit" of the Euler formula in the subspace `span{l, w}`:
`J = l w† − w l†`. -/
def eulerJ (l w : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.vecMulVec l w - Matrix.vecMulVec w l

/-
**Headline — Euler's formula for the density matrix.**
For a real wave-function `φ = cos θ · l + sin θ · w`, the rank-1 density matrix
`φ φ†` decomposes as
`½(l l† + w w†) + ½ cos(2θ)(l l† − w w†) + ½ sin(2θ)(l w† + w l†)`.
This is a purely algebraic identity (double-angle formulas), requiring no
orthonormality of `l, w`.
-/


/-
The Euler "imaginary unit" `J = l w† − w l†` is antisymmetric: `Jᵀ = −J`.
-/


/-
Under orthonormality (`⟪l,l⟫ = ⟪w,w⟫ = 1`, `⟪l,w⟫ = 0`), the Euler imaginary
unit squares to minus the identity of the subspace:
`J² = −(l l† + w w†)`.  Thus `J` genuinely plays the role of `i` on `span{l,w}`.
-/


/-
**"Taking the real part."** The `l`-diagonal entry of the density matrix
`φ φ†` (with `φ = cos θ · l + sin θ · w`) is, under orthonormality,
`cos²θ = ½ + ½ cos(2θ)` — the book's conditional probability
`P(l | l or above)`.
-/


/-
Under orthonormality, the density matrix `φ φ†` of the normalized
wave-function `φ = cos θ · l + sin θ · w` is a genuine rank-1 projector
(idempotent): `(φ φ†)(φ φ†) = φ φ†`.  This is the density matrix of a pure
state.
-/


end BookProof.ChapterE3


