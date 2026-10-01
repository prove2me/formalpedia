-- Prove2me | Definitions.Def_ChapterShannonSampling
-- name    : ChapterShannonSampling
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T04:48:53.999554+00:00
-- url     : https://prove2.me/theorems/f665e9c5-8364-4f6d-a57c-8859e5280baa
-- title:
--   Chapter ShannonSampling
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterShannonSampling.lean`): generated def bundle for ChapterShannonSampling. See BookProof/ChapterShannonSampling.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterShannonSampling.lean

import Mathlib


/-!
# The Whittaker–Shannon sampling theorem

Source: `book.tex`, chapter *"Resolution of the singularity of the ODE x'=x² when the
initial x has uncertainties"*, §*Resolution of the singularity using the uncertainties in x*:

> "Since the Hamiltonian differs from the translation in space by a change of variables
> `y → 1/x`, then using the Whittaker–Shannon interpolation (also called sinc
> interpolation) […] we can completely define the wave-function in coordinate space through
> its values at discrete points."

The book uses the classical sampling theorem as an external fact.  This file **proves** it.

## The statement

Fix a bandwidth parameter `T > 0`.  A *band-limited signal* is the inverse Fourier transform

```
bandSignal F x = ∫ ξ in -T/2..T/2, exp (2πi x ξ) · F ξ
```

of a spectrum `F` supported in the band `[-T/2, T/2]`, which we encode as a function on the
circle `AddCircle T` (a spectrum on the band and its `T`-periodic extension carry the same
information, and this is exactly what makes the Fourier *series* of the spectrum available).

* `bandSignal_sample` — the samples at the lattice `n/T` are the Fourier coefficients of the
  spectrum: `bandSignal F (-(n/T)) = T · fourierCoeff F n`;
* **`bandSignal_hasSum_sinc`** — the Whittaker–Shannon interpolation formula
  `bandSignal F x = ∑ₙ bandSignal F (n/T) · sinc (T x - n)`, an unconditionally convergent
  sum over `n : ℤ`, for every real `x`;
* **`hasSum_sq_samples`** — Parseval for the samples: their squared norms are summable and
  their sum is the energy of the spectrum;
* **`bandSignal_eq_of_samples_eq`** — the consequence the book uses: two band-limited signals
  with the same samples on the lattice `{n/T}` are the *same function*, so a band-limited
  wave-function is completely determined by its values at those discrete points;
* `continuous_bandSignal_lp` — a band-limited signal is a continuous function, so sampling it
  at the lattice points really is evaluation;
* `sinc_intCast` / `sinc_zero` — the interpolation property of the cardinal sine: the `n`-th
  term of the series is the only one that survives at `x = n/T`.

## The proof

Everything is the pairing of the spectrum with the exponential kernel, expanded in the
Fourier basis of `L²` of the circle:

* `integral_exp_mul_ofReal` — the elementary integral `∫_{-T/2}^{T/2} e^{2πiaξ} dξ =
  T · sinc (aT)`, which is where the cardinal sine comes from;
* `kern x` is the `T`-periodic extension of `ξ ↦ e^{2πixξ}` from the band (`AddCircle.liftIoc`),
  a bounded measurable function, hence an element `kernLp x` of `L²`;
* `bandSignal_eq_inner` identifies the signal with the inner product `T · ⟪kernLp x, F⟫`, and
  `inner_kernLp_fourierBasis` computes the inner products of the kernel with the Fourier basis
  as the cardinal sines `sinc (T x + n)`;
* Parseval for the Fourier basis (`HilbertBasis.hasSum_inner_mul_inner`) then gives the
  interpolation formula, and injectivity of `fourierBasis.repr` gives the uniqueness clause.

Everything is `sorry`-free and uses only the standard axioms.
-/

namespace BookProof.ChapterShannonSampling

open MeasureTheory Complex AddCircle intervalIntegral Set
open scoped Real ComplexConjugate

/-! ## The cardinal sine -/

/-- The normalized cardinal sine `sinc u = sin (π u) / (π u)`, with value `1` at `u = 0`. -/
noncomputable def sinc (u : ℝ) : ℝ := if u = 0 then 1 else Real.sin (π * u) / (π * u)







/-! ## The elementary integral -/



section Band

variable {T : ℝ} [hT : Fact (0 < T)]



/-! ## The band-limited signal -/

/-- The band-limited signal with spectrum `F`: the inverse Fourier transform of `F` over the
band `[-T/2, T/2]`. -/
noncomputable def bandSignal (F : AddCircle T → ℂ) (x : ℝ) : ℂ :=
  ∫ ξ in (-(T / 2))..(T / 2), Complex.exp (2 * π * I * x * ξ) * F ξ

/-- The `T`-periodic extension of the exponential kernel `ξ ↦ e^{-2πixξ}` from the band. -/
noncomputable def kern (x : ℝ) : AddCircle T → ℂ :=
  AddCircle.liftIoc T (-(T / 2)) fun ξ => Complex.exp (-(2 * π * I * x * ξ))

theorem kern_coe_apply (x : ℝ) {ξ : ℝ} (hξ : ξ ∈ Ioc (-(T / 2)) (-(T / 2) + T)) :
    kern (T := T) x ξ = Complex.exp (-(2 * π * I * x * ξ)) :=
  AddCircle.liftIoc_coe_apply hξ

theorem norm_kern (x : ℝ) (z : AddCircle T) : ‖kern (T := T) x z‖ = 1 := by
  obtain ⟨ξ, hξ, rfl⟩ : ∃ ξ : ℝ, ξ ∈ Ioc (-(T / 2)) (-(T / 2) + T) ∧ (ξ : AddCircle T) = z :=
    ⟨(equivIoc T (-(T / 2)) z : ℝ), (equivIoc T (-(T / 2)) z).2, by
      conv_rhs => rw [← (equivIoc T (-(T / 2))).symm_apply_apply z]
      rfl⟩
  rw [kern_coe_apply x hξ, Complex.norm_exp]
  have : (-(2 * π * I * x * ξ)).re = 0 := by simp
  simp [this]

theorem measurable_kern (x : ℝ) : Measurable (kern (T := T) x) := by
  have h₁ : Measurable (equivIoc T (-(T / 2))) :=
    (AddCircle.measurePreserving_equivIoc T (a := -(T / 2))).measurable
  have h₂ : Measurable fun ξ : Ioc (-(T / 2)) (-(T / 2) + T) =>
      Complex.exp (-(2 * π * I * x * (ξ : ℝ))) := by
    fun_prop
  exact h₂.comp h₁

theorem memLp_kern (x : ℝ) : MemLp (kern (T := T) x) 2 (haarAddCircle (T := T)) :=
  MemLp.of_bound (measurable_kern x).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun z => by rw [norm_kern]; )

/-- The kernel as an element of `L²` of the circle. -/
noncomputable def kernLp (x : ℝ) : Lp ℂ 2 (haarAddCircle (T := T)) := (memLp_kern x).toLp _

















/-! ## Band-limited signals are continuous -/













end Band

end BookProof.ChapterShannonSampling


