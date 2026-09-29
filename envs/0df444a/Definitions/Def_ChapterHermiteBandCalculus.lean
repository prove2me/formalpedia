-- Prove2me | Definitions.Def_ChapterHermiteBandCalculus
-- name    : ChapterHermiteBandCalculus
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-13T16:26:55.181423+00:00
-- url     : https://prove2.me/theorems/bf6c20d5-6e74-48c6-931c-c1d96e7f6d9b
-- title:
--   The graded band calculus of the product Hermite basis: a real quadratic Hamiltonian has a # band matrix whose entries grow like the degree What is proved
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.HermiteBandCalculus`, source chapter `BookProof/ChapterHermiteBandCalculus.lean`): The graded band calculus of the product Hermite basis: a real quadratic Hamiltonian has a # band matrix whose entries grow like the degree What is proved
--
--   `BookProof.ChapterHermiteProductBasis` makes the product Hermite functions `ψ_α = He_α · e^{-‖x‖²/4} / ‖·‖` an orthonormal basis of `L²(ℝᵈ)` and records the ladder relations `a†ᵢψ_α = √(αᵢ+1) ψ_{α+eᵢ}`, `aᵢψ_α = √αᵢ ψ_{α−eᵢ}`. This chapter turns those relations into a **calculus of band operators**, whose purpose is the input of the weighted Schur gate of `BookProof.ChapterFockWeightedSchurEsa`: a one-particle matrix that is band-limited in the degree, has boundedly many entries per column, and whose entries grow at most like `deg + 1`.
--
--   * `hpsi`, `pgLp_hpsi`, `hcomb` — the normalized Hermite *polynomial* `ψ_α`, its `L²` vector, and the finite combination `Σ_β f_β ψ_β` of Hermite states. * `crePoly_hpsi`, `annPoly_hpsi` — the ladder relations at the level of polynomials. * `Band T r M C g` — the band predicate: `T ψ_α` is a combination of at most `M` Hermite states whose degrees differ from `deg α` by at most `r`, with coefficients bounded by `C · g (deg α)`. The two growths used are `g1 n = √(n+1)` (first order) and `g2 n = n + 1` (second order). * `Band.add`, `Band.smul`, `Band.mono`, `Band.toBand2` — the closure properties. * `band_crePoly`, `band_annPoly` — the ladder operators are first-order band operators with `M = C = 1`. * **`Band.comp`** — the composition of two first-order band operators is a second-order one: `M₁M₂` entries, band `2`, and the growth `2 M₁ C₁ C₂ (deg α + 1)`; the analytic content is `√(deg α + 1) · √(deg γ + 1) ≤ 2 (deg α + 1)` for `|deg γ − deg α| ≤ 1`. * `IsBand1` / `IsBand2` — the existential forms, closed under sums, scalar multiples, finite sums and (for `IsBand1`) composition. * `mulXPoly_eq`, `momPoly_eq` — the coordinate and momentum operators are the ladder combinations `xᵢ = aᵢ† + aᵢ` and `πᵢ = (i/2)(aᵢ† − aᵢ)`, hence first-order. * **`isBand2_fqPoly`** — the headline: the general real quadratic Hamiltonian `fqPoly P Q S b b'` of `BookProof.ChapterFullQuadraticEsa` — an arbitrary Weyl-ordered quadratic form in the coordinates and momenta, plus a first-order term — is a second-order band operator.
--
--   Everything is `sorry`-free and `axiom`-free.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteBandCalculus.lean

import Definitions.Def_ChapterFullQuadraticEsa
import Mathlib

import Mathlib
import Definitions.Def_ChapterContinuityUnitary
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterSirkFinitePrecision

/-!
# The graded band calculus of the product Hermite basis: a real quadratic Hamiltonian has a
# band matrix whose entries grow like the degree

`BookProof.ChapterHermiteProductBasis` makes the product Hermite functions
`ψ_α = He_α · e^{-‖x‖²/4} / ‖·‖` an orthonormal basis of `L²(ℝᵈ)` and records the ladder
relations `a†ᵢψ_α = √(αᵢ+1) ψ_{α+eᵢ}`, `aᵢψ_α = √αᵢ ψ_{α−eᵢ}`.  This chapter turns those
relations into a **calculus of band operators**, whose purpose is the input of the weighted
Schur gate of `BookProof.ChapterFockWeightedSchurEsa`: a one-particle matrix that is
band-limited in the degree, has boundedly many entries per column, and whose entries grow
at most like `deg + 1`.

## What is proved

* `hpsi`, `pgLp_hpsi`, `hcomb` — the normalized Hermite *polynomial* `ψ_α`, its `L²` vector,
  and the finite combination `Σ_β f_β ψ_β` of Hermite states.
* `crePoly_hpsi`, `annPoly_hpsi` — the ladder relations at the level of polynomials.
* `Band T r M C g` — the band predicate: `T ψ_α` is a combination of at most `M` Hermite
  states whose degrees differ from `deg α` by at most `r`, with coefficients bounded by
  `C · g (deg α)`.  The two growths used are `g1 n = √(n+1)` (first order) and
  `g2 n = n + 1` (second order).
* `Band.add`, `Band.smul`, `Band.mono`, `Band.toBand2` — the closure properties.
* `band_crePoly`, `band_annPoly` — the ladder operators are first-order band operators with
  `M = C = 1`.
* **`Band.comp`** — the composition of two first-order band operators is a second-order one:
  `M₁M₂` entries, band `2`, and the growth `2 M₁ C₁ C₂ (deg α + 1)`; the analytic content is
  `√(deg α + 1) · √(deg γ + 1) ≤ 2 (deg α + 1)` for `|deg γ − deg α| ≤ 1`.
* `IsBand1` / `IsBand2` — the existential forms, closed under sums, scalar multiples, finite
  sums and (for `IsBand1`) composition.
* `mulXPoly_eq`, `momPoly_eq` — the coordinate and momentum operators are the ladder
  combinations `xᵢ = aᵢ† + aᵢ` and `πᵢ = (i/2)(aᵢ† − aᵢ)`, hence first-order.
* **`isBand2_fqPoly`** — the headline: the general real quadratic Hamiltonian
  `fqPoly P Q S b b'` of `BookProof.ChapterFullQuadraticEsa` — an arbitrary Weyl-ordered
  quadratic form in the coordinates and momenta, plus a first-order term — is a second-order
  band operator.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.HermiteBand

noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

/-- The normalized product Hermite polynomial `ψ_α = He_α / ‖He_α‖`. -/
def hpsi (α : Fin d →₀ ℕ) : MvPolynomial (Fin d) ℂ :=
  ((hermiteMvNorm α : ℝ) : ℂ)⁻¹ • hermiteMv α



/-- The finite combination of Hermite states with coefficients `f`. -/
abbrev hcomb (f : (Fin d →₀ ℕ) →₀ ℂ) : MvPolynomial (Fin d) ℂ :=
  Finsupp.linearCombination ℂ (hpsi (d := d)) f





/-! ## The band predicate -/

/-- `Band T r M C g`: on every Hermite state `ψ_α`, the operator `T` produces a combination
of at most `M` Hermite states whose degrees differ from `deg α` by at most `r`, with
coefficients bounded by `C · g (deg α)`. -/
def Band (T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ) (r M : ℕ) (C : ℝ)
    (g : ℕ → ℝ) : Prop :=
  ∀ α : Fin d →₀ ℕ, ∃ f : (Fin d →₀ ℕ) →₀ ℂ,
    T (hpsi α) = hcomb f ∧ f.support.card ≤ M ∧
      (∀ β ∈ f.support, ((β.degree : ℤ) - (α.degree : ℤ)).natAbs ≤ r) ∧
      (∀ β, ‖f β‖ ≤ C * g α.degree)

/-- The growth of a first-order (ladder) operator. -/
def g1 : ℕ → ℝ := fun n => Real.sqrt ((n : ℝ) + 1)

/-- The growth of a second-order (quadratic) operator. -/
def g2 : ℕ → ℝ := fun n => (n : ℝ) + 1













/-! ## Degrees -/







/-! ## The two ladder operators are first-order band operators -/





/-! ## Composition: a product of two first-order operators is second-order -/



open BookProof.NavierStokesFlow.DifferentialL2 BookProof.FullQuadratic

/-- A first-order band operator. -/
def IsBand1 (T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ) : Prop :=
  ∃ (M : ℕ) (C : ℝ), 0 ≤ C ∧ Band T 1 M C g1

/-- A second-order band operator. -/
def IsBand2 (T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ) : Prop :=
  ∃ (M : ℕ) (C : ℝ), 0 ≤ C ∧ Band T 2 M C g2























/-! ## The basic operators -/













/-! ## The quadratic Hamiltonian -/









end

end BookProof.HermiteBand


