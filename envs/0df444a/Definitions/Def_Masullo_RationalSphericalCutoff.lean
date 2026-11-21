-- Prove2me | Definitions.Def_Masullo_RationalSphericalCutoff
-- name    : Masullo_RationalSphericalCutoff
-- status  : Definition
-- author  : @marozols
-- created : 2026-11-21T02:54:17.182168+00:00
-- url     : https://prove2.me/theorems/020d523c-1460-4a7d-8996-61fd22de398e
-- title:
--   Actual rational spherical adelic tests, prime differences and masked orbital Hilbert spaces
-- statement:
--   Over the rational adeles, a normalized representative of log-norm $t$ has real component $e^t$ and integral finite component with integral inverse. An admissible Schwartz–Bruhat test vanishes at zero and has zero additive Haar integral. At the finite place above $p$ we take the actual uniformizer-idele difference of a spherical pure tensor. For any test family and mask, its orbital image consists of square-integrable vectors which vanish outside the mask and coincide on it with an ordinary rational orbital sum on every normalized representative. The supported space consists of all such vectors vanishing off the mask.
-- source:
--   A. M. Masullo, The Music of the Primes, Definition 5.3.1.2 and Theorem 11.1.2.1(2).

import Mathlib
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_IdeleProductMeasure

open NumberField IsDedekindDomain MeasureTheory Set
open scoped ContDiff Classical

namespace MasulloAudit.RationalSphericalCutoff

abbrev Adele := AdeleRing (𝓞 ℚ) ℚ
abbrev Idele := Adeleˣ

noncomputable local instance : MeasurableSpace Adele :=
  (borel (InfiniteAdeleRing ℚ)).prod (borel (FiniteAdeleRing (𝓞 ℚ) ℚ))

noncomputable def realComponent (y : Adele) : ℝ :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ y.1).1
    ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩

noncomputable def integers := AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ

def Representative (t : ℝ) (z : Idele) : Prop :=
  (z : Adele).2 ∈ integers ∧ (↑z⁻¹ : Adele).2 ∈ integers ∧ realComponent z = Real.exp t

def Admissible (test : Adele → ℂ) : Prop :=
  test ∈ AdelicFourier.schwartzBruhat ℚ ∧ test 0 = 0 ∧
    ∀ (m : Measure Adele) [m.IsAddHaarMeasure], (∫ x, test x ∂m) = 0

noncomputable def primeSources (p : Nat.Primes) : Set (Adele → ℂ) :=
  let step := AutomorphicForm.uniformizerIdele ℚ (Rat.HeightOneSpectrum.primesEquiv.symm p)
  {test | Admissible test ∧ ∃ (source : Adele → ℂ) (f : ℝ → ℂ),
    Admissible source ∧ ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
    (∀ y, source y = if y.2 ∈ integers then f (realComponent y) else 0) ∧
    ∀ y, test y = source y - source ((↑step⁻¹ : Adele) * y)}

def image (μ : Measure ℝ) (s : Set ℝ) (B : Set (Adele → ℂ)) : Set (Lp ℂ 2 μ) :=
  {w | ∃ test ∈ B, ∀ᵐ t ∂μ, (t ∉ s → w t = 0) ∧
    (t ∈ s → ∀ z : Idele, Representative t z →
      HasSum (fun q : ℚˣ => test (algebraMap ℚ Adele (q : ℚ) * z)) (w t))}

def supported (μ : Measure ℝ) (s : Set ℝ) : Set (Lp ℂ 2 μ) :=
  {w | ∀ᵐ t ∂μ, t ∉ s → w t = 0}

end MasulloAudit.RationalSphericalCutoff


