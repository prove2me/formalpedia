-- Prove2me | Definitions.Def_ChapterMajoranaProp76
-- name    : ChapterMajoranaProp76
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-08T01:40:08.727882+00:00
-- url     : https://prove2.me/theorems/9fe838b9-2763-4db9-971a-5d7df28f5658
-- title:
--   Majorana properties 76
-- statement:
--   Formal definitions for the Majorana properties 76 of the timepiece Lean 4 formalization (module `BookProof.MajoranaProp76`, source chapter `BookProof/ChapterMajoranaProp76.lean`).
--
--   `book.tex` **Proposition 76** introduces the **energy transform**
--
--   `𝓔 := Θ_{L²} ∘ 𝓕_P(−p⁰) ∘ Θ_{L²}⁻¹`
--
--   — the Pauli–Fourier transform `𝓕_P` in the *time* coordinate, conjugated by the real-linear identification `Θ_{L²}` — and states that `𝓔` is **unitary**, "for the same conjugation reason" as Proposition 73: a conjugate of a unitary by an inner-product-preserving bijection is again unitary. The composite `𝓔 ∘ 𝓕_M` (with the Majorana–Fourier transform `𝓕_M`) is then the unitary **energy–momentum transform**.
--
--   The book's proof is purely structural:
--
--   * the Pauli–Fourier transform `𝓕_P` is unitary on `L²` (Plancherel — Mathlib's `MeasureTheory.Lp.fourierTransformₗᵢ`, a genuine `≃ₗᵢ[ℂ]`); * conjugating a unitary by a linear isometry equivalence `Θ` yields a unitary (`𝓔` is unitary); * composing two unitaries yields a unitary (`𝓔 ∘ 𝓕_M` is unitary).
--
--   This file formalizes exactly that structural core, using **Note 4**'s definition of unitarity (surjective and diagonal-inner-preserving, `⟪f x, f x⟫ = ⟪x, x⟫`), as already used for Proposition 5. Working with the bare-function predicate `IsNote4Unitary` keeps the two closure lemmas (`note4_comp`, `note4_conj`) maximally general: they need no linearity of the unitary being conjugated, only that the conjugator `Θ` preserves inner products and is bijective. We then instantiate on the concrete Mathlib `L²`-Fourier transform to exhibit the actual `𝓕_P` as a Note-4 unitary and to build the concrete energy transform `𝓔`.
--
--   The `𝓔 ∘ 𝓗_M` "spherical" energy–momentum transform of Proposition 76 involves the Majorana–Hankel transform `𝓗_M` and is **deliberately not formalized** (off the Hankel line); the linear `𝓔 ∘ 𝓕_M` branch is what we discharge here. This also stays **off the gravity line**.
--
--   Everything is `sorry`-free and `axiom`-free.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMajoranaProp76.lean

import Mathlib

/-!
# Chapter "Real representations, CPT theorem and the relativistic position operator",
§"Fourier-Majorana Transform", **Proposition 76** — the energy transform `𝓔` and the
energy–momentum transform `𝓔 ∘ 𝓕_M` are unitary

`book.tex` **Proposition 76** introduces the **energy transform**

  `𝓔 := Θ_{L²} ∘ 𝓕_P(−p⁰) ∘ Θ_{L²}⁻¹`

— the Pauli–Fourier transform `𝓕_P` in the *time* coordinate, conjugated by the
real-linear identification `Θ_{L²}` — and states that `𝓔` is **unitary**, "for the
same conjugation reason" as Proposition 73: a conjugate of a unitary by an
inner-product-preserving bijection is again unitary.  The composite
`𝓔 ∘ 𝓕_M` (with the Majorana–Fourier transform `𝓕_M`) is then the unitary
**energy–momentum transform**.

The book's proof is purely structural:

* the Pauli–Fourier transform `𝓕_P` is unitary on `L²` (Plancherel — Mathlib's
  `MeasureTheory.Lp.fourierTransformₗᵢ`, a genuine `≃ₗᵢ[ℂ]`);
* conjugating a unitary by a linear isometry equivalence `Θ` yields a unitary
  (`𝓔` is unitary);
* composing two unitaries yields a unitary (`𝓔 ∘ 𝓕_M` is unitary).

This file formalizes exactly that structural core, using **Note 4**'s definition
of unitarity (surjective and diagonal-inner-preserving, `⟪f x, f x⟫ = ⟪x, x⟫`),
as already used for Proposition 5.  Working with the bare-function predicate
`IsNote4Unitary` keeps the two closure lemmas (`note4_comp`, `note4_conj`)
maximally general: they need no linearity of the unitary being conjugated, only
that the conjugator `Θ` preserves inner products and is bijective.  We then
instantiate on the concrete Mathlib `L²`-Fourier transform to exhibit the actual
`𝓕_P` as a Note-4 unitary and to build the concrete energy transform `𝓔`.

The `𝓔 ∘ 𝓗_M` "spherical" energy–momentum transform of Proposition 76 involves
the Majorana–Hankel transform `𝓗_M` and is **deliberately not formalized** (off
the Hankel line); the linear `𝓔 ∘ 𝓕_M` branch is what we discharge here.  This
also stays **off the gravity line**.

Everything is `sorry`-free and `axiom`-free.
-/

open scoped InnerProductSpace

namespace BookProof.ChapterMajoranaProp76

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **Note 4 unitarity** for a bare function `f : H → K` between inner-product
spaces: `f` is surjective and preserves the diagonal inner product
`⟪f x, f x⟫ = ⟪x, x⟫`.  (For a linear `f`, polarization upgrades this to full
inner-product preservation; the book states and uses the diagonal form.) -/
def IsNote4Unitary (𝕜 : Type*) [RCLike 𝕜] {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] (f : H → K) : Prop :=
  Function.Surjective f ∧ ∀ x, (inner 𝕜 (f x) (f x) : 𝕜) = (inner 𝕜 x x : 𝕜)

section
variable {H K L : Type*}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]
  [NormedAddCommGroup L] [InnerProductSpace 𝕜 L]







end

/-! ## The energy transform `𝓔 = Θ ∘ V ∘ Θ⁻¹` and the composite `𝓔 ∘ 𝓕_M` -/

section
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]

/-- The **energy transform** `𝓔 = Θ ∘ V ∘ Θ⁻¹`, the conjugate of the time-Fourier
transform `V = 𝓕_P(−p⁰)` by the real-linear identification `Θ = Θ_{L²}`. -/
def energyTransform (Θ : H ≃ₗᵢ[𝕜] K) (V : H → H) : K → K :=
  (Θ : H → K) ∘ V ∘ (Θ.symm : K → H)





end

/-! ## Concrete instantiation: the `L²`-Fourier transform is a Note-4 unitary -/

open MeasureTheory

variable {E F : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]





end BookProof.ChapterMajoranaProp76


