-- Prove2me | Definitions.Def_ChapterA3i
-- name    : ChapterA3i
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T05:38:21.592186+00:00
-- url     : https://prove2.me/theorems/d2e016b3-4267-4f3f-a25b-56a37dbb905c
-- title:
--   Chapter A3i
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterA3i.lean`): generated def bundle for ChapterA3i. See BookProof/ChapterA3i.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterA3i.lean

import Definitions.Def_ChapterA3
import Mathlib


/-!
# Chapter A, §A.3 — Lemma 48: the bridge `Λ(Σ ∘ T ∘ Σ⁻¹) = Υ(T)`

Source: `book.tex` line 5458 (**Lemma 48**), work-package **N4** of
`FORMALIZATION_ROADMAP.md`.

This module supplies the **`Σ` / bridge half of Lemma 48**, the piece connecting
the two concrete double covers of the Lorentz group built earlier:

* the **Pauli / `SL(2,ℂ)`** cover `Υ : SL(2,ℂ) → O(1,3)` of
  `ChapterA3h.lean` (Note 47), `Υ^μ_ν(T) σ^ν = T† σ^μ T`;
* the **Majorana / Pinor** cover `Λ : Pin(3,1) → O(1,3)` of `ChapterA3c.lean`
  (Prop 46), `Λ(S)^μ_ν iγ^ν = S⁻¹ iγ^μ S`.

The book's explicit real-linear isomorphism `Σ : Pauli → Pinor` (book eq. 5468)
matches the `±`-eigenspaces of `γ⁰γ³` (on `Pinor = ℂ⁴`, real form) with those of
`σ³` (on `Pauli = ℂ²`, real form). Concretely, in the Majorana basis of
`ChapterA3.lean`, taking `M₊ = e₀ + e₃`, `M₋ = e₀ - e₃`, the isomorphism `Σ` is
the integer `4×4` matrix

`Σ = !![1,0,0,-1; 0,-1,-1,0; 0,-1,1,0; 1,0,0,1]`,

which satisfies `Σ Σᵀ = 2` (so `Σ⁻¹ = ½ Σᵀ`).

For `T ∈ SL(2,ℂ)` we realise `Σ ∘ T ∘ Σ⁻¹ ∈ Spin⁺(3,1)` concretely as the real
`4×4` matrix `Spinor T := Σ · Tᵣ · (½ Σᵀ)`, where `Tᵣ = Treal T` is the real
`4×4` form of the `ℂ`-linear action of `T` on `ℂ²` in the ordered real basis
`(P₊, iP₊, P₋, iP₋)`.  Its inverse (when `det T = 1`) is `SpinorInv T`, built the
same way from the adjugate `T⁻¹ = !![d,-b;-c,a]`.

The **headline** is the bridge identity (proved as a pure polynomial identity in
the entries of `T`, no `det T = 1` needed):

`SpinorInv T · iγ^μ · Spinor T = ∑_ν Υ(T)^ν_μ · iγ^ν`,

i.e. conjugation by `Spinor T` acts on the Majorana basis exactly by the (real)
matrix `Υ(T)ᵀ` — the Pinor cover `Λ` of `Σ T Σ⁻¹` equals the Pauli cover `Υ` of
`T` (transposed by the `Λ`/`Υ` index conventions).  Combined with
`Spinor T · SpinorInv T = 1` (which *does* use `det T = 1`), we get the same
statement with the genuine inverse `(Spinor T)⁻¹`.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open Matrix
open scoped ComplexConjugate

namespace BookProof.ChapterA3

/-! ## The isomorphism `Σ` -/

/-- The integer matrix of the Pauli→Pinor isomorphism `Σ` (book eq. 5468) in the
Majorana basis of `ChapterA3.lean`, with `M₊ = e₀+e₃`, `M₋ = e₀-e₃`. -/
def SigmaZ : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1,0,0,-1; 0,-1,-1,0; 0,-1,1,0; 1,0,0,1]



/-- The complex form of `Σ`. -/
noncomputable def SigmaC : Matrix (Fin 4) (Fin 4) ℂ :=
  (Int.castRingHom ℂ).mapMatrix SigmaZ



/-! ## The real form of `T` and the spinor matrices -/

/-- The real `4×4` form of the `ℂ`-linear action of a `2×2` complex matrix `T` on
`ℂ²`, in the ordered real basis `(P₊, iP₊, P₋, iP₋)` of `Pauli = ℂ²`. -/
noncomputable def Treal (T : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  !![ ((T 0 0).re : ℂ), -((T 0 0).im : ℂ), ((T 0 1).re : ℂ), -((T 0 1).im : ℂ);
      ((T 0 0).im : ℂ),  ((T 0 0).re : ℂ), ((T 0 1).im : ℂ),  ((T 0 1).re : ℂ);
      ((T 1 0).re : ℂ), -((T 1 0).im : ℂ), ((T 1 1).re : ℂ), -((T 1 1).im : ℂ);
      ((T 1 0).im : ℂ),  ((T 1 0).re : ℂ), ((T 1 1).im : ℂ),  ((T 1 1).re : ℂ) ]

/-- The adjugate `!![d,-b;-c,a]` of `T = !![a,b;c,d]` (equal to `T⁻¹` when
`det T = 1`). -/
noncomputable def adj2 (T : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![ T 1 1, -(T 0 1); -(T 1 0), T 0 0 ]

/-- The concrete realisation of `Σ ∘ T ∘ Σ⁻¹ ∈ Spin⁺(3,1)` as a real `4×4`
matrix, `Spinor T = Σ · Treal T · (½ Σᵀ)`. -/
noncomputable def Spinor (T : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  SigmaC * Treal T * ((2⁻¹ : ℂ) • SigmaCᵀ)

/-- The candidate inverse of `Spinor T`, built from the adjugate of `T`. -/
noncomputable def SpinorInv (T : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  SigmaC * Treal (adj2 T) * ((2⁻¹ : ℂ) • SigmaCᵀ)

/-
The real form is multiplicative: `Treal (A B) = Treal A · Treal B` (the real
form of a `ℂ`-linear map is a ring homomorphism `Mat₂(ℂ) → Mat₄(ℝ)`).
-/










/-! ## The bridge identity -/

/-
**The bridge identity (pure algebra).**  Conjugation of the Majorana basis by
`Spinor T` is given by the Pauli-cover matrix `Υ(T)` (transposed by the index
conventions):
`SpinorInv T · iγ^μ · Spinor T = ∑_ν Υ(T)^ν_μ · iγ^ν`.
This holds as a polynomial identity in the entries of `T`; `det T = 1` is *not*
needed.
-/










end BookProof.ChapterA3


