-- Prove2me | Definitions.Def_ChapterFreeFieldConstraint
-- name    : ChapterFreeFieldConstraint
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T22:39:04.146352+00:00
-- url     : https://prove2.me/theorems/8c561578-344e-4912-acfd-34547a05a0b8
-- title:
--   Source: `book.tex`, chapter *"Free field parametrization in Classical Statistical Field Theory and Navier-Stokes equatio ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.FreeFieldConstraint`, source chapter `BookProof/ChapterFreeFieldConstraint.lean`).
--
--   Source: `book.tex`, chapter *"Free field parametrization in Classical Statistical Field Theory and Navier-Stokes equations"*, section *"Free field parametrization in Statistical Field Theory"* (displayed equation at line ~3948).
--
--   For a Hamiltonian depending on the fields up to first-order derivatives, the book imposes the *momentum constraint* `i D_x = 0`. It then states that, **because the Hamiltonian commutes with the constraint**, the following two commutator identities hold (for the field `φ⁽⁰⁾` and the momentum `p₍₁₎`):
--
--   ``` [[i D_x, φ⁽⁰⁾], H] = -[i D_x, [H, φ⁽⁰⁾]] [[i D_x, p₍₁₎], H] = -[i D_x, [H, p₍₁₎]] ```
--
--   Both are instances of a single, purely algebraic fact about the commutator bracket `⁅a, b⁆ = a·b − b·a` in any (non-commutative, associative) ring: **if the constraint `D` commutes with the Hamiltonian `H`, then for every operator `A`**
--
--   ``` ⁅⁅D, A⁆, H⁆ = -⁅D, ⁅H, A⁆⁆. ```
--
--   This is a direct consequence of the Jacobi identity together with `⁅D, H⁆ = 0`. This file formalizes:
--
--   * `bracket` — the ring commutator, with `bracket_antisymm` and `bracket_self`; * `bracket_jacobi` — the Jacobi identity for the commutator bracket; * `constraint_commute_symm` — `⁅D, H⁆ = 0 ↔ ⁅H, D⁆ = 0`; * `constraint_commutation_identity` — the headline `⁅⁅D, A⁆, H⁆ = -⁅D, ⁅H, A⁆⁆` (book.tex ~3948), stated for a general operator `A`; * `constraint_commutation_identity_field` / `constraint_commutation_identity_momentum` — the two literal book instances (`A = φ⁽⁰⁾` and `A = p₍₁₎`); * `constraint_preserved_under_bracket` — if the constraint commutes with both `H` and `A`, it commutes with `⁅H, A⁆` (the constraint is conserved by the Hamiltonian flow of a compatible operator).
--
--   Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`).
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFreeFieldConstraint.lean

import Mathlib
import Mathlib

import Mathlib

import Mathlib

/-!
# Chapter "Free field parametrization in Classical Statistical Field Theory and
Navier-Stokes equations" — the momentum-constraint commutation identity

Source: `book.tex`, chapter *"Free field parametrization in Classical Statistical
Field Theory and Navier-Stokes equations"*, section *"Free field parametrization
in Statistical Field Theory"* (displayed equation at line ~3948).

For a Hamiltonian depending on the fields up to first-order derivatives, the book
imposes the *momentum constraint* `i D_x = 0`.  It then states that, **because the
Hamiltonian commutes with the constraint**, the following two commutator
identities hold (for the field `φ⁽⁰⁾` and the momentum `p₍₁₎`):

```
[[i D_x, φ⁽⁰⁾], H] = -[i D_x, [H, φ⁽⁰⁾]]
[[i D_x, p₍₁₎], H] = -[i D_x, [H, p₍₁₎]]
```

Both are instances of a single, purely algebraic fact about the commutator
bracket `⁅a, b⁆ = a·b − b·a` in any (non-commutative, associative) ring: **if the
constraint `D` commutes with the Hamiltonian `H`, then for every operator `A`**

```
⁅⁅D, A⁆, H⁆ = -⁅D, ⁅H, A⁆⁆.
```

This is a direct consequence of the Jacobi identity together with `⁅D, H⁆ = 0`.
This file formalizes:

* `bracket` — the ring commutator, with `bracket_antisymm` and `bracket_self`;
* `bracket_jacobi` — the Jacobi identity for the commutator bracket;
* `constraint_commute_symm` — `⁅D, H⁆ = 0 ↔ ⁅H, D⁆ = 0`;
* `constraint_commutation_identity` — the headline `⁅⁅D, A⁆, H⁆ = -⁅D, ⁅H, A⁆⁆`
  (book.tex ~3948), stated for a general operator `A`;
* `constraint_commutation_identity_field` / `constraint_commutation_identity_momentum`
  — the two literal book instances (`A = φ⁽⁰⁾` and `A = p₍₁₎`);
* `constraint_preserved_under_bracket` — if the constraint commutes with both `H`
  and `A`, it commutes with `⁅H, A⁆` (the constraint is conserved by the
  Hamiltonian flow of a compatible operator).

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace BookProof.FreeFieldConstraint

variable {R : Type*} [Ring R]

/-- The commutator bracket `⁅a, b⁆ = a·b − b·a` on a (non-commutative) ring; this
is the algebraic form of the commutator of operators used throughout the free-field
chapter. -/
def bracket (a b : R) : R := a * b - b * a





















end BookProof.FreeFieldConstraint


