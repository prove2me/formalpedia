-- Prove2me | Definitions.Def_ChapterParity
-- name    : ChapterParity
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T06:24:45.541481+00:00
-- url     : https://prove2.me/theorems/5b5d1fec-1ab8-479d-a27d-4d13af46c191
-- title:
--   Chapter Parity
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterParity.lean`): generated def bundle for ChapterParity. See BookProof/ChapterParity.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterParity.lean

import Definitions.Def_ChapterA3
import Mathlib


/-!
# Chapter "On the physical parity transformation and antiparticles" — the finite algebraic core

This file formalizes the self-contained, finite-dimensional algebraic content of the
`book.tex` chapter *"On the physical parity transformation and antiparticles"*
(`book.tex` line ~7522).  The chapter's central physical thesis — that at the quantum
level all fields are **real representations** (self-adjoint operators), so that CP and
P coincide and the (generalized) parity transformation is **order four** — rests on a
handful of concrete linear-algebra facts, which are what we discharge here.

The surrounding physical modelling (canonical quantization of a real Hilbert space, the
Standard-Model Lagrangian, path-integral measures) is left as prose.

Deliverable groups:

* **Hermitian decomposition of a field.** *"Any non-Hermitian field can always be
  decomposed into a sum of two Hermitian fields"* (Lee–Wick, quoted in the chapter):
  every square complex matrix `X` is `A + i B` with `A`, `B` Hermitian.
* **The Higgs (generalized) parity is order four.** The internal part of the Higgs
  parity transformation `φ ↦ i σ₂ φ` is `i σ₂`, which satisfies `(i σ₂)² = -1` and hence
  `(i σ₂)⁴ = 1` while `(i σ₂)² ≠ 1`: the parity is a genuine `ℤ₄` (order-4) symmetry.
* **The fermion parity operator `i γ⁰` is order four ⇒ the double cover is `Pin(3,1)`.**
  On Majorana spinors the parity acts through `i γ⁰ = mgamma 0` of the concrete `A3`
  model; `(i γ⁰)² = -1` (order four), in contrast to the naive Dirac `γ⁰` for which
  `(γ⁰)² = +1`.  This `-1` is exactly the invariant distinguishing `Pin(3,1)` from
  `Pin(1,3)`.
* **The Gell-Mann outer-automorphism signs.** The complex conjugation of the eight
  `SU(3)` Gell-Mann matrices realizes the `ℤ₂` outer automorphism with the sign pattern
  the chapter uses for the parity transformation of the gluon fields: the real
  generators (`λ¹, λ³, λ⁴, λ⁶, λ⁸`) are fixed and the imaginary ones (`λ², λ⁵, λ⁷`) are
  negated.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

open Matrix
open scoped ComplexConjugate

namespace BookProof.ChapterParity

/-! ## 1. Hermitian decomposition of an arbitrary field -/

variable {n : Type*}

/-- The Hermitian part `A = ½ (X + Xᴴ)` of a field `X`. -/
noncomputable def hermPart (X : Matrix n n ℂ) : Matrix n n ℂ := (2 : ℂ)⁻¹ • (X + Xᴴ)

/-- The "imaginary" Hermitian part `B = (2i)⁻¹ (X − Xᴴ)`, so that `X = A + i B`. -/
noncomputable def antihermPart (X : Matrix n n ℂ) : Matrix n n ℂ :=
  (2 * Complex.I)⁻¹ • (X - Xᴴ)







/-! ## 2. The Higgs (generalized) parity `i σ₂` is order four -/

/-- The Pauli matrix `σ₂`. -/
noncomputable def pauli2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- The internal part `i σ₂` of the Higgs (generalized) parity transformation
`φ ↦ i σ₂ φ`. -/
noncomputable def higgsParity : Matrix (Fin 2) (Fin 2) ℂ := Complex.I • pauli2









/-! ## 3. The fermion parity `i γ⁰` is order four ⇒ the double cover is `Pin(3,1)` -/

open BookProof.ChapterA3







/-! ## 4. The Gell-Mann matrices and the outer-automorphism (parity) signs -/

/-- The eight Gell-Mann generators `λ¹, …, λ⁸` of `SU(3)` (indexed `0, …, 7`). -/
noncomputable def gellMann : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ
  | 0 => !![0,1,0; 1,0,0; 0,0,0]
  | 1 => !![0,-Complex.I,0; Complex.I,0,0; 0,0,0]
  | 2 => !![1,0,0; 0,-1,0; 0,0,0]
  | 3 => !![0,0,1; 0,0,0; 1,0,0]
  | 4 => !![0,0,-Complex.I; 0,0,0; Complex.I,0,0]
  | 5 => !![0,0,0; 0,0,1; 0,1,0]
  | 6 => !![0,0,0; 0,0,-Complex.I; 0,Complex.I,0]
  | 7 => ((1 : ℝ) / Real.sqrt 3) • !![1,0,0; 0,1,0; 0,0,-2]

/-- The complex-conjugation eigenvalue of `λ^a`: `+1` for the real generators
(`λ¹, λ³, λ⁴, λ⁶, λ⁸`) and `-1` for the imaginary ones (`λ², λ⁵, λ⁷`). -/
def gellMannConjSign : Fin 8 → ℂ
  | 1 => -1
  | 4 => -1
  | 6 => -1
  | _ => 1





end BookProof.ChapterParity


