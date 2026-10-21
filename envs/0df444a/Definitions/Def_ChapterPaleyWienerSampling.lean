-- Prove2me | Definitions.Def_ChapterPaleyWienerSampling
-- name    : ChapterPaleyWienerSampling
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-20T16:33:42.368932+00:00
-- url     : https://prove2.me/theorems/c82b70fd-5eb1-4839-87fc-7936c16a2d4d
-- title:
--   The Lean 4 theorem `continuous_fourier` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterPaleyWienerSampling.lean`): generated def bundle for ChapterPaleyWienerSampling. See BookProof/ChapterPaleyWienerSampling.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterPaleyWienerSampling.lean

import Theorems.Thm_BookProof_ChapterShannonSampling_exists_rep

import Definitions.Def_ChapterShannonSampling
import Mathlib
import Theorems.Thm_BookProof_ChapterShannonSampling_half_add_period


/-!
# Sampling for band-limited functions on the line (the Paley–Wiener picture)

`BookProof/ChapterShannonSampling.lean` proves the Whittaker–Shannon sampling theorem in the
*spectral* picture: the signal is *defined* as the inverse Fourier transform `bandSignal F` of a
square-integrable spectrum `F` over the band `[-T/2, T/2]`.  That left one gap, recorded there as
an honest boundary: the identification of that class with the genuinely band-limited functions of
the line, i.e. with the functions whose *own* Fourier transform vanishes outside the band.

This file closes that gap.  A function `f : ℝ → ℂ` is `BandLimited T` when it is continuous,
integrable, and its Fourier transform `𝓕 f` vanishes outside the band `|ξ| ≤ T/2`.  Then:

* `BandLimited.integrable_fourier` — the spectrum is continuous with compact support, hence
  integrable and bounded, so Fourier inversion applies;
* **`BandLimited.eq_bandSignal`** — `f` *is* the band-limited signal of its own spectrum, that
  spectrum being viewed (`bandSpectrumLp`) as a square-integrable function on the circle of
  circumference `T`;
* **`BandLimited.hasSum_sinc`** — the classical sampling theorem on the line:
  `f x = ∑_{n ∈ ℤ} f (n/T) · sinc (T x - n)` for every real `x`, an unconditionally convergent
  series;
* **`BandLimited.eq_of_samples_eq`** — a band-limited function is determined by its samples at
  the lattice `{n/T}`;
* **`BandLimited.hasSum_sq_samples`** — Parseval for the samples: `∑_n ‖f (n/T)‖²` converges to
  `T · ∫_ℝ ‖𝓕 f‖²`.

Everything is `sorry`-free and uses only the standard axioms.
-/

namespace BookProof.ChapterPaleyWienerSampling

open MeasureTheory Complex AddCircle Set
open scoped Real FourierTransform
open BookProof.ChapterShannonSampling (sinc bandSignal exists_rep half_add_period)

/-- A *band-limited function of bandwidth `T`*: a continuous integrable function on the line
whose Fourier transform vanishes outside the band `|ξ| ≤ T/2`. -/
structure BandLimited (T : ℝ) (f : ℝ → ℂ) : Prop where
  /-- The function is continuous. -/
  continuous : Continuous f
  /-- The function is integrable, so that its Fourier transform is defined. -/
  integrable : Integrable f
  /-- The Fourier transform vanishes outside the band. -/
  spectrum_support : ∀ ξ : ℝ, T / 2 < |ξ| → 𝓕 f ξ = 0

namespace BandLimited

variable {T : ℝ} {f g : ℝ → ℂ}

/-- The Fourier transform of an integrable function is continuous. -/
theorem continuous_fourier (hf : BandLimited T f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by apply continuous_inner) hf.integrable

/-- The spectrum of a band-limited function has compact support. -/
theorem hasCompactSupport_fourier (hf : BandLimited T f) : HasCompactSupport (𝓕 f) := by
  refine HasCompactSupport.intro (K := Icc (-(T / 2)) (T / 2)) isCompact_Icc ?_
  intro ξ hξ
  refine hf.spectrum_support ξ ?_
  rcases lt_or_ge (T / 2) |ξ| with h | h
  · exact h
  · exact absurd (abs_le.mp h) (by simpa [Set.mem_Icc] using hξ)



/-- The spectrum of a band-limited function is bounded. -/
theorem exists_bound_fourier (hf : BandLimited T f) : ∃ C, ∀ ξ : ℝ, ‖𝓕 f ξ‖ ≤ C :=
  hf.hasCompactSupport_fourier.exists_bound_of_continuous hf.continuous_fourier

end BandLimited

section Spectrum

variable {T : ℝ} [hT : Fact (0 < T)] {f g : ℝ → ℂ}

/-- The spectrum of `f`, viewed as a function on the circle of circumference `T`: the
`T`-periodic extension of `𝓕 f` from the band `(-T/2, T/2]`. -/
noncomputable def bandSpectrum (T : ℝ) [Fact (0 < T)] (f : ℝ → ℂ) : AddCircle T → ℂ :=
  AddCircle.liftIoc T (-(T / 2)) (𝓕 f)

theorem bandSpectrum_coe_apply {ξ : ℝ} (hξ : ξ ∈ Ioc (-(T / 2)) (-(T / 2) + T)) :
    bandSpectrum T f ξ = 𝓕 f ξ :=
  show AddCircle.liftIoc T (-(T / 2)) (𝓕 f) ξ = 𝓕 f ξ from AddCircle.liftIoc_coe_apply hξ

theorem measurable_bandSpectrum (hf : BandLimited T f) : Measurable (bandSpectrum T f) := by
  have h₁ : Measurable (equivIoc T (-(T / 2))) :=
    (AddCircle.measurePreserving_equivIoc T (a := -(T / 2))).measurable
  have h₂ : Measurable fun ξ : Ioc (-(T / 2)) (-(T / 2) + T) => 𝓕 f (ξ : ℝ) :=
    (hf.continuous_fourier.comp continuous_subtype_val).measurable
  exact show Measurable (AddCircle.liftIoc T (-(T / 2)) (𝓕 f)) from h₂.comp h₁

theorem norm_bandSpectrum_le (hf : BandLimited T f) :
    ∃ C, ∀ z : AddCircle T, ‖bandSpectrum T f z‖ ≤ C := by
  obtain ⟨C, hC⟩ := hf.exists_bound_fourier
  refine ⟨C, fun z => ?_⟩
  obtain ⟨ξ, hξ, rfl⟩ := exists_rep (T := T) z
  rw [bandSpectrum_coe_apply hξ]
  exact hC ξ

theorem memLp_bandSpectrum (hf : BandLimited T f) :
    MemLp (bandSpectrum T f) 2 (haarAddCircle (T := T)) := by
  obtain ⟨C, hC⟩ := norm_bandSpectrum_le hf
  exact MemLp.of_bound (measurable_bandSpectrum hf).aestronglyMeasurable C
    (Filter.Eventually.of_forall hC)

/-- The spectrum of a band-limited function as an element of `L²` of the circle. -/
noncomputable def bandSpectrumLp (hf : BandLimited T f) : Lp ℂ 2 (haarAddCircle (T := T)) :=
  (memLp_bandSpectrum hf).toLp _





namespace BandLimited











end BandLimited

end Spectrum

end BookProof.ChapterPaleyWienerSampling


