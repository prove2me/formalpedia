-- Prove2me | Definitions.Def_RiemannMasullo_LCAFourierConvolution
-- name    : RiemannMasullo_LCAFourierConvolution
-- status  : Definition
-- author  : @dga471
-- created : 2026-11-21T00:53:25.059398+00:00
-- url     : https://prove2.me/theorems/432360f5-e07f-476a-aa30-3c6f8fa8face
-- title:
--   Fourier and convolution integrals on locally compact abelian groups
-- statement:
--   The Fourier integral uses the conjugate character. Multiplicative convolution integrates the second function at the left-translated argument. The Tamagawa Fourier integral uses the character attached to multiplication by the frequency, as in Appendix A.3.1.1.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L63-L77

import Mathlib
noncomputable section
namespace RiemannMasullo
open MeasureTheory Set
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [MeasurableSpace G]

def lcaFourier (μ : Measure G) (f : G → ℂ) (χ : PontryaginDual G) : ℂ :=
  ∫ x, f x * star (χ x : ℂ) ∂μ

def lcaConvolution (μ : Measure G) (f g : G → ℂ) (x : G) : ℂ :=
  ∫ y, f y * g (y⁻¹ * x) ∂μ

variable {R : Type*} [CommRing R] [TopologicalSpace R] [MeasurableSpace R]

def tamagawaFourier (μ : Measure R) (ψ : R → Circle) (f : R → ℂ) (y : R) : ℂ :=
  ∫ x, f x * star (ψ (x * y) : ℂ) ∂μ

end RiemannMasullo


