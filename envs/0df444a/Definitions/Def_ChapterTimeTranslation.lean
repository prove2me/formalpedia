-- Prove2me | Definitions.Def_ChapterTimeTranslation
-- name    : ChapterTimeTranslation
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T11:12:50.740514+00:00
-- url     : https://prove2.me/theorems/184247a8-edfd-4fc7-905b-3616ce4b6497
-- title:
--   Chapter TimeTranslation
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterTimeTranslation.lean`): generated def bundle for ChapterTimeTranslation. See BookProof/ChapterTimeTranslation.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterTimeTranslation.lean

import Definitions.Def_ChapterReconstruct
import Mathlib


/-!
# Chapter "Reconstructing the classical trajectory of any isolated quantum system"
— the density-matrix / trace form of the main result
*"Time translation is a stochastic process if and only if it is deterministic"*

This file formalizes the **literal density-matrix statement** of the section
*"Time translation is a stochastic process if and only if it is deterministic"*
(`book.tex` line ~2613), one of the book's stated *"main results"*.

The book reduces the existence of a group action of a Wigner symmetry group on the
probability distribution to the equality, for every pure state `ρ_g = |Ψ⟩⟨Ψ|`,
every outcome `A = a` (rank-one projection `P_a = |e_a⟩⟨e_a|`) and every unitary
`U`, of the two Born probabilities

* `tr(diag(ρ_g) · U P_a U†)` — the probability obtained if the state first
  *collapses* to its diagonal (classical) part and then the transformation acts, and
* `tr(ρ_g · U P_a U†)` — the probability obtained if the transformation acts on the
  full quantum state.

The book then observes this equality is equivalent to the vanishing of the
off-diagonal Born sum `∑_{k≠b} conj(U k a)·Ψ k·conj(Ψ b)·U b a`, which is in turn
equivalent to `U` being *deterministic* (each column has at most one nonzero
entry). The off-diagonal core `↔` determinism is already established in
`BookProof.ChapterReconstruct` (`offDiag_eq_zero_iff_isDeterministic`,
`offDiag_unit_iff`). This file supplies the missing **density-matrix layer**: it
identifies the two matrix traces with the full/collapsed Born sums, shows their
difference is exactly the off-diagonal sum, and packages the headline equivalence

    (∀ a Ψ, tr(diag(ρ Ψ) · U P_a U†) = tr(ρ Ψ · U P_a U†)) ↔ IsDeterministic U

both over all states and over pure states (`∑ ‖Ψ k‖² = 1`).

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

open scoped BigOperators
open Finset Matrix
open BookProof.ChapterReconstruct

namespace BookProof.ChapterTimeTranslation

variable {n : ℕ}

/-- The pure-state density matrix `ρ = |Ψ⟩⟨Ψ|`, with entries `ρ i j = Ψ i · conj(Ψ j)`. -/
def rho (Ψ : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => Ψ i * (starRingEnd ℂ) (Ψ j)

/-- The diagonal (collapsed) part of a matrix: keep the diagonal, zero the rest.
This is the wave-function collapse in the measurement basis. -/
def diagPart (M : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => if i = j then M i j else 0

/-- The rank-one projection `P_a = |e_a⟩⟨e_a|` onto the basis outcome `a`. -/
def proj (a : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => if i = a ∧ j = a then 1 else 0

/-- The transformed measurement operator `M_a = U P_a U†`. -/
noncomputable def measOp (U : Matrix (Fin n) (Fin n) ℂ) (a : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  U * proj a * Uᴴ

/-
Entries of the measurement operator: `(U P_a U†) k l = U k a · conj(U l a)`.
-/


/-
The "full" Born probability is the trace of `ρ · M_a`; expanded it is the
double sum `∑_{i,k} conj(U i a)·Ψ i · conj(Ψ k)·U k a`.
-/


/-
The "collapsed" Born probability is the trace of `diag(ρ) · M_a`; expanded it
is the diagonal sum `∑_i |Ψ i|²·|U i a|²`.
-/








end BookProof.ChapterTimeTranslation


