-- Prove2me | Definitions.Def_ChapterReconstruct
-- name    : ChapterReconstruct
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T04:43:49.90324+00:00
-- url     : https://prove2.me/theorems/276005e4-6fcd-489c-8e2d-1606028c2dc3
-- title:
--   Chapter Reconstruct
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterReconstruct.lean`): generated def bundle for ChapterReconstruct. See BookProof/ChapterReconstruct.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterReconstruct.lean

import Mathlib


/-!
# Chapter "Reconstructing the classical trajectory of any isolated quantum system"
— a symmetry acts on probability distributions iff it is deterministic

This file formalizes the self-contained linear-algebra core of the section
*"Time translation is a stochastic process if and only if it is deterministic"*
(Chapter *"Reconstructing the classical trajectory of any isolated quantum
system"*, `book.tex` line ~2613).

The book's setup: a Wigner symmetry acts on the wave-function by a unitary
matrix `U` with entries `U k a`.  It observes that the induced map on the
*probability distributions* (obtained after wave-function collapse / the Born
rule) is well-defined — i.e. there is a genuine group action on distributions —
**if and only if** `U` is *deterministic*, meaning each column of `U` has at
most one nonzero entry (`U m a` and `U l a` cannot both be nonzero for `l ≠ m`).

The precise mathematical fact the book extracts (its displayed computation) is
that, for a fixed column `a`, the "off-diagonal Born sum"

```
S_a(Ψ) = ∑_{k ≠ b} conj(U k a) · Ψ k · conj(Ψ b) · U b a
```

vanishes for **every** state `Ψ` iff `conj(U m a) · U l a = 0` for all `l ≠ m`
(the determinism condition for that column).

* Forward direction: if `U` is deterministic then every off-diagonal term
  already contains the vanishing factor `conj(U k a) · U b a`.
* Backward direction: the book exhibits the witness `Ψ ∝ δ_{·m} + δ_{·l}`; a
  rigorous argument needs a second complex phase (`Ψ ∝ δ_{·m} + i δ_{·l}`) to
  kill the imaginary part as well, which is the standard polarization of a
  Hermitian form.  We use the family `Ψ = δ_{·m} + z δ_{·l}` for `z ∈ ℂ`.

We model `U` and `Ψ` as plain functions (`Fin n → Fin n → ℂ`, `Fin n → ℂ`) to
avoid matrix-API friction; no unitarity hypothesis is needed for this algebraic
equivalence, and the condition over all `Ψ` is equivalent (by homogeneity) to
the book's condition over unit vectors, recorded in `offDiag_unit_iff`.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

open scoped BigOperators
open Finset

namespace BookProof.ChapterReconstruct

variable {n : ℕ}

/-- A transformation `U` is *deterministic in column `a`* when that column has at
most one nonzero entry: `conj(U m a) · U l a = 0` for all `l ≠ m`. -/
def IsDeterministicCol (U : Fin n → Fin n → ℂ) (a : Fin n) : Prop :=
  ∀ l m : Fin n, l ≠ m → (starRingEnd ℂ) (U m a) * U l a = 0

/-- `U` is *deterministic* when every column has at most one nonzero entry. -/
def IsDeterministic (U : Fin n → Fin n → ℂ) : Prop :=
  ∀ a : Fin n, IsDeterministicCol U a

/-- The off-diagonal Born sum for column `a` and state `Ψ`:
`∑_{k ≠ b} conj(U k a) · Ψ k · conj(Ψ b) · U b a`. -/
noncomputable def offDiag (U : Fin n → Fin n → ℂ) (a : Fin n) (Ψ : Fin n → ℂ) : ℂ :=
  ∑ k : Fin n, ∑ b : Fin n,
    (if k = b then 0
      else (starRingEnd ℂ) (U k a) * Ψ k * (starRingEnd ℂ) (Ψ b) * U b a)

/-
The off-diagonal sum equals the full bilinear product minus its diagonal:
`S_a(Ψ) = (∑ₖ conj(U k a)·Ψ k)·(∑_b conj(Ψ b)·U b a) − ∑ₖ conj(U k a)·Ψ k·conj(Ψ k)·U k a`.
-/


/-
**Forward direction.** If column `a` of `U` is deterministic, the
off-diagonal Born sum vanishes for every state `Ψ`.
-/


/-
**Backward direction.** If the off-diagonal Born sum vanishes for every
state `Ψ`, then column `a` of `U` is deterministic.
-/






/-
**Book's exact statement (unit-vector form).** Restricting to unit states
(pure density matrices) does not change the equivalence: the off-diagonal Born
sum vanishes on all unit states iff `U` is deterministic.
-/


end BookProof.ChapterReconstruct


