-- Prove2me | Definitions.Def_ChapterParityHiggs
-- name    : ChapterParityHiggs
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T10:45:44.017987+00:00
-- url     : https://prove2.me/theorems/7111784e-863a-4ec9-ad3b-fcfdea80985f
-- title:
--   Chapter ParityHiggs
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterParityHiggs.lean`): generated def bundle for ChapterParityHiggs. See BookProof/ChapterParityHiggs.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterParityHiggs.lean

import Definitions.Def_ChapterParity
import Mathlib


/-!
# Chapter "On the physical parity transformation and antiparticles" — the Higgs is a
real representation (pseudoreal ⊗ pseudoreal = real)

This file continues the finite algebraic core of the `book.tex` chapter *"On the physical
parity transformation and antiparticles"* (`book.tex` line ~7522, §"Majorana spinors in
the Standard Model"), begun in `ChapterParity` / `ChapterParityQL`.

The chapter's central physical thesis is that at the quantum level **all fields are real
representations** of the symmetry group.  For the electroweak Higgs doublet `φ` this is the
Majorana-type reality ("pseudoreality") condition quoted in the chapter,

  `i σ₂ φ = i τ₂ φ*`,

where `σ₂` is the custodial `SU(2)` Pauli matrix and `τ₂` is the gauge `SU(2)_L` Pauli
matrix.  Because `σ₂` and `τ₂` act on **different** doublet indices, the reality condition
is realized on the tensor product `ℂ² ⊗ ℂ²` by the antilinear operator

  `C(φ) = (τ₂ ⊗ σ₂) φ*`.

The mathematical content is the classical representation-theoretic fact that

  **a tensor product of two quaternionic (pseudoreal) structures is a real structure.**

A single `SU(2)` doublet is *pseudoreal*: the antilinear operator `C₀(φ) = σ₂ φ*` squares
to `-1` (it is a quaternionic structure, so a single doublet carries **no** real
structure).  But the *bidoublet* `τ₂ ⊗ σ₂` squares to `+1`, i.e. it is a genuine **real
structure** (an antilinear involution) — which is exactly why the Higgs *is* a real
representation, even though neither factor alone is.

## Contents

* `realityOp M` — the antilinear operator `v ↦ M *ᵥ v*`, and `realityOp_realityOp`:
  `C_M ∘ C_M = (M · M*) *ᵥ ·`, so `C_M` is an involution (real structure) iff
  `M · M* = 1` and squares to `-1` (quaternionic structure) iff `M · M* = -1`.
* `pauli2_map_conj` : `σ₂* = -σ₂`; `pauli2_pseudoreal` : `σ₂ · σ₂* = -1` — a single
  doublet is pseudoreal (`higgsDoublet_pseudoreal` : `C₀² = -1`).
* `kronecker_map_conj` : entrywise conjugation distributes over the Kronecker product.
* `pseudoreal_kron_pseudoreal_real` : the general statement — if `A·A* = -1` and
  `B·B* = -1` then `(A⊗B)·(A⊗B)* = 1`.
* `higgsReal := σ₂ ⊗ σ₂`; `higgsReal_mul_conj` : `(τ₂⊗σ₂)·(τ₂⊗σ₂)* = 1`, and the headline
  `higgs_real_structure` : `C ∘ C = id`, so the Higgs bidoublet carries a real structure —
  the Higgs is a real representation.

The surrounding physical modelling (the full Standard-Model Lagrangian, the custodial
symmetry) is left as prose.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

open Matrix
open scoped Kronecker
open scoped ComplexConjugate

namespace BookProof.ChapterParityHiggs

open BookProof.ChapterParity

/-! ## 1. The antilinear reality operator and its square -/

/-- The antilinear "reality" operator `C_M(v) = M *ᵥ v*` (matrix `M` times the entrywise
complex conjugate of `v`).  A *real structure* is such a `C_M` with `C_M ∘ C_M = id`; a
*quaternionic (pseudoreal) structure* is one with `C_M ∘ C_M = -id`. -/
noncomputable def realityOp {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) (v : I → ℂ) : I → ℂ :=
  M *ᵥ (fun i => conj (v i))



/-! ## 2. A single `SU(2)` doublet is pseudoreal -/







/-! ## 3. Pseudoreal ⊗ pseudoreal = real (the general statement) -/





/-! ## 4. The Higgs bidoublet carries a real structure -/

/-- The internal operator `τ₂ ⊗ σ₂` of the Higgs Majorana condition `iσ₂ φ = iτ₂ φ*`,
acting on the bidoublet `ℂ² ⊗ ℂ² ≅ ℂ⁴`.  Both factors are the Pauli matrix `σ₂`
(`τ₂ = σ₂` as matrices), acting on distinct doublet indices. -/
noncomputable def higgsReal : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := pauli2 ⊗ₖ pauli2





end BookProof.ChapterParityHiggs


