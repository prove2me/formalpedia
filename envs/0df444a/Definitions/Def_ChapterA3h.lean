-- Prove2me | Definitions.Def_ChapterA3h
-- name    : ChapterA3h
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-04T07:32:08.340979+00:00
-- url     : https://prove2.me/theorems/18545f14-11b5-433f-b9cf-06938800b758
-- title:
--   Chapter A3h
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterA3h.lean`): generated def bundle for ChapterA3h. See BookProof/ChapterA3h.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterA3h.lean

import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3b
import Definitions.Def_ChapterA3c
import Mathlib


/-!
# Chapter A, §A.3 — Note 47: the covering map `Υ : SL(2,ℂ) → O(1,3)`

This file formalizes **Note 47** of `FORMALIZATION_ROADMAP.md` (book §A.3,
line 5440), the `SL(2,ℂ)` side of **Lemma 48**.  The book defines a two-to-one
surjection `Υ : SL(2,ℂ) → SO⁺(1,3)` by
`Υ^μ_ν(T) σ^ν = T† σ^μ T`, where `σ⁰ = 1` and `σ^j` are the Pauli matrices.

We build the concrete `2×2` Pauli model and prove:

* `pauliσ_herm` — each `σ^μ` is Hermitian.
* `pauliσ_trace` — the trace-orthogonality `tr(σ^μ σ^ν) = 2 δ^{μν}`.
* `pauli_expand` — every `2×2` complex matrix is `∑_μ (½ tr(σ^μ M)) σ^μ`, so the
  four Pauli matrices are a basis of `Mat₂(ℂ)`.
* `UpsilonC` / `upsilon_recon` — the (complex) coefficient matrix `Υ(T)` with
  `T† σ^ν T = ∑_μ Υ(T)^μ_ν σ^μ`.
* `upsilonC_antihom` — `Υ(T U) = Υ(U) Υ(T)` (an anti-homomorphism, since
  `(TU)† = U† T†`; the book's "homomorphism" is this with the group law read on
  the image).
* `Upsilon` / `upsilonC_real` — the entries of `Υ(T)` are **real**, giving the
  real Lorentz matrix `Upsilon T`.
* `det_pauli_comb` — `det(∑_ν x_ν σ^ν) = x₀² − x₁² − x₂² − x₃²`, the Minkowski
  norm as a determinant (the geometric heart of the construction).
* `upsilon_mem_lorentz` — for `T ∈ SL(2,ℂ)` (`det T = 1`), `Υ(T) ∈ O(1,3)`.

`Σ` and the full Lemma-48 identity `Λ(S) = Υ(Σ⁻¹ S Σ)` (matching the
`γ⁰γ³`/`σ³` eigenspaces) remain future work; the group-level Lorentz image of
`Spin⁺(3,1)` is already covered via the exponential route in `ChapterA3g.lean`.
-/

open Matrix
open scoped ComplexConjugate

namespace BookProof.ChapterA3

/-! ## The Pauli matrices -/

/-- The four Pauli matrices `σ^μ`: `σ⁰ = 1` and the three Pauli matrices. -/
noncomputable def pauliσ : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => !![1,0;0,1]
  | 1 => !![0,1;1,0]
  | 2 => !![0,-Complex.I;Complex.I,0]
  | 3 => !![1,0;0,-1]





/-- The Pauli coefficient functional `c_μ(M) = ½ tr(σ^μ M)`. -/
noncomputable def pauliCoeff (M : Matrix (Fin 2) (Fin 2) ℂ) (μ : Fin 4) : ℂ :=
  2⁻¹ * (pauliσ μ * M).trace



/-
The Pauli coefficient of a Pauli combination recovers the coefficient.
-/


/-! ## The map `Υ` -/

/-- The complex coefficient matrix `Υ(T)`, `Υ(T)^μ_ν = ½ tr(σ^μ T† σ^ν T)`. -/
noncomputable def UpsilonC (T : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun μ ν => pauliCoeff (Tᴴ * pauliσ ν * T) μ

/-
Reconstruction: `T† σ^ν T = ∑_μ Υ(T)^μ_ν σ^μ`.
-/


/-
`Υ` is an anti-homomorphism: `Υ(T U) = Υ(U) Υ(T)`.
-/


/-! ## Reality of `Υ` -/

/-
The entries of `Υ(T)` are real (fixed by complex conjugation).
-/


/-- The real Lorentz matrix `Υ(T)`. -/
noncomputable def Upsilon (T : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun μ ν => (UpsilonC T μ ν).re

/-
The complexification of the real `Υ(T)` is the complex `Υ(T)`.
-/


/-! ## The Minkowski norm as a determinant -/

/-- The Minkowski quadratic form `Q(x) = x₀² − x₁² − x₂² − x₃²`. -/
def Qc (x : Fin 4 → ℂ) : ℂ := (x 0)^2 - (x 1)^2 - (x 2)^2 - (x 3)^2



/-
Under `Υ(T)`, `T† (∑ x_ν σ^ν) T = ∑_μ (Υ(T) x)_μ σ^μ`.
-/


/-
`Υ(T)` preserves the Minkowski form when `det T = 1`.
-/


/-! ## Polarization -/

/-- The bilinear form `x ↦ xᵀ M x` of a matrix. -/
noncomputable def bilC (M : Matrix (Fin 4) (Fin 4) ℂ) (x : Fin 4 → ℂ) : ℂ :=
  ∑ i, ∑ j, x i * M i j * x j

/-
**Polarization.** A symmetric `4×4` complex matrix is determined by its
quadratic form.
-/


/-
The bilinear form of the (complexified) Minkowski metric is `Qc`.
-/


/-
Conjugation identity `xᵀ (Aᵀ M A) x = (A x)ᵀ M (A x)`.
-/


/-
`toC minkowskiMat` is symmetric.
-/




/-! ## `Υ(T) ∈ O(1,3)` -/

/-
The real metric-preservation identity `Υ(T)ᵀ η Υ(T) = η`.
-/


/-
**Note 47.** For `T ∈ SL(2,ℂ)`, `Υ(T)` lands in the Lorentz group `O(1,3)`.
-/


end BookProof.ChapterA3


