-- Prove2me | Definitions.Def_ChapterBell
-- name    : ChapterBell
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T03:23:48.662272+00:00
-- url     : https://prove2.me/theorems/2e3866fd-7e53-4631-bf53-ea9f53cca83d
-- title:
--   Chapter Bell
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterBell.lean`): generated def bundle for ChapterBell. See BookProof/ChapterBell.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterBell.lean

import Mathlib


/-!
# Chapter "Reconstructing the classical trajectory of any isolated quantum system",
  §"Do the Bell inequalities hold?"

This file formalizes the self-contained mathematical content flagged in the `book.tex`
section *"Do the Bell inequalities hold?"* (`book.tex` line ~3175).  The chapter's own
concession is that *"the Bell inequalities (despite being mathematically valid inequalities)
involve unrealistic assumptions"* — so the two mathematically formalizable facts are:

1. **The Bell / CHSH inequality is a valid inequality for any local hidden-variable model.**
   If a "standard statistical theory" is described by a probability distribution on a
   phase space and the four dichotomic (`±1`-valued, or more generally `[-1,1]`-valued)
   measurement outcomes `A₀, A₁` (Alice) and `B₀, B₁` (Bob) are ordinary random variables
   on that space, then the CHSH correlator obeys
   `|⟨A₀B₀⟩ + ⟨A₀B₁⟩ + ⟨A₁B₀⟩ − ⟨A₁B₁⟩| ≤ 2`.

2. **Quantum mechanics violates it.**  With Alice's observables `σ_z, σ_x`, Bob's
   observables `(σ_z ± σ_x)/√2`, and the maximally entangled Bell state
   `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2`, the same CHSH combination of expectation values equals
   `2√2 > 2` (the Tsirelson value).  This is exactly why the classical bound is
   *"innocuous"* as a distinguishing criterion: a complete statistical theory (quantum
   mechanics) sits outside the local hidden-variable class the inequality characterizes.

## Contents

* `chsh_pointwise` — the elementary pointwise algebraic inequality: for
  `a₀,a₁,b₀,b₁ ∈ [-1,1]`, `|a₀b₀ + a₀b₁ + a₁b₀ − a₁b₁| ≤ 2`.
* `chsh_local` — the measure-theoretic Bell/CHSH inequality: for any probability measure
  `μ` and `[-1,1]`-valued random variables, the CHSH correlator is `≤ 2` in absolute value.
* `chsh_quantum_value` — the quantum expectation value of the CHSH operator in the Bell
  state `|Φ⁺⟩` equals `2√2`.
* `chsh_quantum_violates_local_bound` — `2 < 2√2`: quantum mechanics exceeds the classical
  Bell bound.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

open scoped BigOperators
open MeasureTheory

namespace BookProof.ChapterBell

/-! ## Part A — the classical Bell / CHSH inequality (local hidden variables) -/



variable {Ω : Type*} [MeasurableSpace Ω]



/-! ## Part B — the quantum violation (Tsirelson value `2√2`) -/

open Matrix
open scoped Kronecker ComplexConjugate

/-- Pauli `σ_x`. -/
def sx : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Pauli `σ_z`. -/
def sz : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- Alice's first observable `A₀ = σ_z`. -/
def A0 : Matrix (Fin 2) (Fin 2) ℂ := sz

/-- Alice's second observable `A₁ = σ_x`. -/
def A1 : Matrix (Fin 2) (Fin 2) ℂ := sx

/-- Bob's first observable `B₀ = (σ_z + σ_x)/√2`. -/
noncomputable def B0 : Matrix (Fin 2) (Fin 2) ℂ := (1 / (Real.sqrt 2 : ℂ)) • (sz + sx)

/-- Bob's second observable `B₁ = (σ_z − σ_x)/√2`. -/
noncomputable def B1 : Matrix (Fin 2) (Fin 2) ℂ := (1 / (Real.sqrt 2 : ℂ)) • (sz - sx)

/-- The CHSH operator `A₀⊗B₀ + A₀⊗B₁ + A₁⊗B₀ − A₁⊗B₁` on the two-qubit space. -/
noncomputable def chshOp : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  A0 ⊗ₖ B0 + A0 ⊗ₖ B1 + A1 ⊗ₖ B0 - A1 ⊗ₖ B1

/-- The maximally entangled Bell state `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2`. -/
noncomputable def bellState : (Fin 2 × Fin 2) → ℂ :=
  fun p => if p = (0, 0) then (1 / (Real.sqrt 2 : ℂ))
           else if p = (1, 1) then (1 / (Real.sqrt 2 : ℂ)) else 0

/-- The CHSH expectation value `⟨Φ⁺| S |Φ⁺⟩`. -/
noncomputable def chshValue : ℂ := (star bellState) ⬝ᵥ (chshOp *ᵥ bellState)





end BookProof.ChapterBell


