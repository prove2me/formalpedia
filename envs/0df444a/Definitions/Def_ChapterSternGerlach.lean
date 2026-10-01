-- Prove2me | Definitions.Def_ChapterSternGerlach
-- name    : ChapterSternGerlach
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T04:55:53.375655+00:00
-- url     : https://prove2.me/theorems/b6e04141-41c5-4c4b-b081-a585ecdc1d8c
-- title:
--   Chapter SternGerlach
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSternGerlach.lean`): generated def bundle for ChapterSternGerlach. See BookProof/ChapterSternGerlach.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSternGerlach.lean

import Mathlib


/-!
# Chapter "Black hole information paradox and the Stern-Gerlach experiment"

This file formalizes the self-contained mathematical content of the section
*"Black hole information paradox and the Stern-Gerlach experiment"* (and the
preceding *"The Stern-Gerlach experiment"*) of the chapter *"Wave-function
collapse versus Euler's formula"* (`book.tex`, lines ~3344–3476).

The book's central self-contained claim there is:

> *"there is always a unitary transformation such that the corresponding
> probability distribution is necessarily the constant distribution, for all
> initial states in the same orthogonal basis."*

In Born's rule, applying a unitary `U` to a basis state `eⱼ` and measuring in the
same basis gives the probability distribution `i ↦ |Uᵢⱼ|²`.  The claim is that
for **any** finite dimension `n` there is a unitary `U` whose *every* entry has
`|Uᵢⱼ|² = 1/n`, i.e. every basis input produces the *uniform* (constant) output
distribution.  This is exactly the statement that a "black hole" transformation
can turn any incoming basis state into a maximally mixed (information-erased)
distribution while remaining unitary.

We realize this with the (unnormalized) **discrete Fourier transform matrix**
`Uᵢⱼ = exp(2πi·i·j/n)/√n`, a complex Hadamard matrix.  For `n = 2` this is the
usual Hadamard gate `(1/√2)·[[1,1],[1,-1]]`, the two-state case the book uses to
model the Stern-Gerlach experiment.

We also record the concrete numerical fact behind the sequential Stern-Gerlach
experiment: a `π/4` rotation of the two-state spin gives the `50%/50%`
distribution, `cos²(π/4) = sin²(π/4) = 1/2`.

All results are `sorry`-free and axiom-clean (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace BookProof.ChapterSternGerlach

open Complex Matrix Finset

/-- The (normalized) discrete Fourier transform matrix on `Fin n`:
`Uᵢⱼ = exp(2πi·i·j/n)/√n`.  A complex Hadamard matrix; for `n = 2` it is the
Hadamard gate. -/
noncomputable def dftMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => Complex.exp (2 * Real.pi * Complex.I * (i.val * j.val) / n) / Real.sqrt n



















end BookProof.ChapterSternGerlach


