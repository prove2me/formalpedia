-- Prove2me | Definitions.Def_ChapterWeylHamiltonian
-- name    : ChapterWeylHamiltonian
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T23:15:23.023144+00:00
-- url     : https://prove2.me/theorems/8ced1ef5-6a88-446f-8f60-dfe347c17ad1
-- title:
--   Source: `book.tex`, chapter *"Timepiece and the Gribov ambiguity"*, §*"Free electromagnetic field: an exact example"* / ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.WeylHamiltonian`, source chapter `BookProof/ChapterWeylHamiltonian.lean`).
--
--   Source: `book.tex`, chapter *"Timepiece and the Gribov ambiguity"*, §*"Free electromagnetic field: an exact example"* / §*"Renormalization, the mass gap and the Millennium prize"* (lines ~7480–7520), and the parallel Weyl-gauge Hamiltonian in the chapter *"Quantization due to time-evolution: Yang-Mills and Classical Statistical Field Theory"*, §*"Pure SU(3) Yang-Mills theory"* (line ~7060).
--
--   The book reduces the Yang–Mills Hamiltonian, after BRST gauge fixing, to the **Weyl-gauge Hamiltonian density**
--
--   `H_W(x) = ½ πⁱₐ πⁱₐ + ½ Bᵢₐ Bᵢₐ`
--
--   (a sum of squares of the *self-adjoint* electric-field operators `πⁱₐ` and magnetic-field operators `Bᵢₐ`; the sign is a convention of the classical action). The central claim used in the mass-gap discussion is:
--
--   > "We can easily conclude that the Hamiltonian in the Weyl gauge is **positive > definite** and thus … Yang-Mills theory can be reformulated with or without a > mass gap without any observable consequences."
--
--   Positive-definiteness (bounded below by `0`) is exactly what makes the mass-gap argument of §"Mass gap" applicable, so this file formalizes that self-contained mathematical fact.
--
--   Work on an arbitrary complex Hilbert space `H` (the physical state space). Model the electric-field operators `π : Fin n → H →L[ℂ] H` and the magnetic-field operators `B : Fin m → H →L[ℂ] H` as bounded **self-adjoint** operators (`IsSelfAdjoint`, the physical requirement that they are observables). Define the Weyl-gauge Hamiltonian
--
--   `weylHamiltonian π B = ½ • (∑ i, (π i)² ) + ½ • (∑ a, (B a)² )`.
--
--   * `selfAdjoint_sq_isPositive` — the square of a self-adjoint operator is a positive operator (its expectation values are `≥ 0`). * `smul_nonneg_isPositive` — a nonnegative real multiple of a positive operator is positive. * `weylHamiltonian_isPositive` — **the Weyl-gauge Hamiltonian is a positive operator** (`(weylHamiltonian π B).IsPositive`); this is the book's "positive definite" statement. * `weylHamiltonian_expectation_nonneg` — every expectation value is `≥ 0` (`0 ≤ re ⟪weylHamiltonian π B x, x⟫`), the operational form of "positive definite" / "bounded below by `0`". * `weylHamiltonian_isSelfAdjoint` — the Weyl-gauge Hamiltonian is itself self-adjoint (a genuine observable).
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterWeylHamiltonian.lean

import Mathlib
import Mathlib

import Mathlib

import Mathlib

/-!
# Chapter "Timepiece and the Gribov ambiguity", §"Renormalization, the mass gap and the Millennium
prize"

Source: `book.tex`, chapter *"Timepiece and the Gribov ambiguity"*,
§*"Free electromagnetic field: an exact example"* / §*"Renormalization, the mass
gap and the Millennium prize"* (lines ~7480–7520), and the parallel Weyl-gauge
Hamiltonian in the chapter *"Quantization due to time-evolution: Yang-Mills and
Classical Statistical Field Theory"*, §*"Pure SU(3) Yang-Mills theory"*
(line ~7060).

The book reduces the Yang–Mills Hamiltonian, after BRST gauge fixing, to the
**Weyl-gauge Hamiltonian density**

  `H_W(x) = ½ πⁱₐ πⁱₐ + ½ Bᵢₐ Bᵢₐ`

(a sum of squares of the *self-adjoint* electric-field operators `πⁱₐ` and
magnetic-field operators `Bᵢₐ`; the sign is a convention of the classical
action). The central claim used in the mass-gap discussion is:

> "We can easily conclude that the Hamiltonian in the Weyl gauge is **positive
> definite** and thus … Yang-Mills theory can be reformulated with or without a
> mass gap without any observable consequences."

Positive-definiteness (bounded below by `0`) is exactly what makes the mass-gap
argument of §"Mass gap" applicable, so this file formalizes that self-contained
mathematical fact.

## What is proved

Work on an arbitrary complex Hilbert space `H` (the physical state space).
Model the electric-field operators `π : Fin n → H →L[ℂ] H` and the
magnetic-field operators `B : Fin m → H →L[ℂ] H` as bounded **self-adjoint**
operators (`IsSelfAdjoint`, the physical requirement that they are observables).
Define the Weyl-gauge Hamiltonian

  `weylHamiltonian π B = ½ • (∑ i, (π i)² ) + ½ • (∑ a, (B a)² )`.

* `selfAdjoint_sq_isPositive` — the square of a self-adjoint operator is a
  positive operator (its expectation values are `≥ 0`).
* `smul_nonneg_isPositive` — a nonnegative real multiple of a positive operator
  is positive.
* `weylHamiltonian_isPositive` — **the Weyl-gauge Hamiltonian is a positive
  operator** (`(weylHamiltonian π B).IsPositive`); this is the book's
  "positive definite" statement.
* `weylHamiltonian_expectation_nonneg` — every expectation value is `≥ 0`
  (`0 ≤ re ⟪weylHamiltonian π B x, x⟫`), the operational form of
  "positive definite" / "bounded below by `0`".
* `weylHamiltonian_isSelfAdjoint` — the Weyl-gauge Hamiltonian is itself
  self-adjoint (a genuine observable).
-/

namespace BookProof.WeylHamiltonian

open ContinuousLinearMap
open scoped BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]





/-- The Weyl-gauge Yang–Mills Hamiltonian density
`H_W = ½ Σᵢ πᵢ² + ½ Σₐ Bₐ²`, built from the self-adjoint electric-field
operators `π` and magnetic-field operators `B`. -/
noncomputable def weylHamiltonian {n m : ℕ}
    (π : Fin n → H →L[ℂ] H) (B : Fin m → H →L[ℂ] H) : H →L[ℂ] H :=
  ((1 / 2 : ℝ) : ℂ) • (∑ i, (π i ∘L π i)) + ((1 / 2 : ℝ) : ℂ) • (∑ a, (B a ∘L B a))







end BookProof.WeylHamiltonian


