-- Prove2me | Definitions.Def_Arxiv1808_03267_Basic
-- name    : Arxiv1808_03267_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T05:11:55.332497+00:00
-- url     : https://prove2.me/theorems/f5ece00c-ffce-4180-a6c5-569ca11a6314
-- title:
--   Object field, Fresnel propagation, phase-mask camera intensity, power spectrum and autocorrelation
-- statement:
--   Objects of the main text of Stern and Katz (2018), eqs. (1)-(2), PDF pp. 1-2.
--
--   1. **Transverse plane.** Object-plane coordinates $(x,y)$ and second-layer (camera) coordinates $(x',y')$ both range over $\mathbb{R}^2$ with Lebesgue measure.
--   2. **Object field.** A thin object with complex transmission $T$ is illuminated through the first scattering layer by a speckle field $E_{illum}$. The field just after the object is $E_{object}(x)=E_{illum}(x)\,T(x)$.
--   3. **Propagation to the second layer.** At wavelength $\lambda$ and distance $L$, the field arriving at the second layer is given by the paraxial (Fresnel) diffraction integral
--   $$E(x',L)=\frac{e^{ikL}}{i\lambda L}\int_{\mathbb{R}^2}E(x)\,\exp\Big(\frac{i\pi\,|x'-x|^2}{\lambda L}\Big)\,dx,\qquad k=\frac{2\pi}{\lambda}.$$
--   4. **Thin second layer.** An infinitely thin second layer is a phase mask: for one realization $\varphi:\mathbb{R}^2\to\mathbb{R}$ of its random phase, the field on its far side is $e^{i\varphi(x')}E(x',L)$.
--   5. **Camera intensity.** The camera images the external facet of the second layer: $I_{camera}(x')=\big|e^{i\varphi(x')}E(x',L)\big|^2$.
--   6. **Fourier transform and power spectrum.** $\mathcal{F}(E)(u)=\int E(x)\,e^{-2\pi i\langle x,u\rangle}\,dx$ and $\mathcal{F}^{-1}(g)(x)=\int g(u)\,e^{2\pi i\langle u,x\rangle}\,du$; the power spectrum of $E$ is $|\mathcal{F}(E)(u)|^2$.
--   7. **Autocorrelation (eq. 2).** $A(x)=(E\star E)(x)=\int_{\mathbb{R}^2}\overline{E(y)}\,E(x+y)\,dy$.
--
--   **Formalization Note** The paper does not write the propagation law from the object to the second layer; it only uses its far-field (Fraunhofer) form. The Fresnel integral of item 3 is the standard paraxial law whose far-field limit is that form. The phase $\varphi$ is an arbitrary real function: the statements hold for every realization of the random mask, so no probability law on $\varphi$ is needed. All integrals are Lebesgue (Bochner) integrals; each statement assumes the integrability that makes them meaningful.
-- source:
--   Stern and Katz, Non-invasive Focusing Through Scattering Layers Using Speckle-Correlations, arXiv:1808.03267v1 (2018), main text (unsectioned), eqs. (1)-(2) and surrounding paragraphs, PDF pp. 1-2

import Mathlib

/-!
G. Stern and O. Katz, *Non-invasive Focusing Through Scattering Layers Using Speckle-Correlations*,
arXiv:1808.03267v1 (2018): the object field, the propagation to the second scattering layer, the
thin random-phase-mask layer, the camera intensity, the power spectrum and the field
autocorrelation of the main text, eqs. (1)-(2), PDF pp. 1-2.
-/

open MeasureTheory
open scoped FourierTransform

noncomputable section

namespace Arxiv1808_03267

/-- The transverse plane, with coordinates `(x, y)` (object plane) or `(x', y')` (second layer and
camera), as the Euclidean space `ℝ²` with Lebesgue measure. Main text, p. 1-2. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Main text, p. 1-2: the field just after the thin object,
`E_object(x,y) = E_illum(x,y) T(x,y)`, where `E_illum` is the (speckle) field illuminating the
object through the first layer and `T` is the object's transmission. -/
def objectField (Eillum T : Plane → ℂ) (x : Plane) : ℂ :=
  Eillum x * T x

/-- The field `E(x', y', L)` arriving at the second layer after the object field `E` propagates a
distance `L` at wavelength `lam` (main text, p. 2, the field entering eq. (1)). The paper does not
write the propagation law; this is the standard paraxial (Fresnel) diffraction integral
`E(x', L) = e^{ikL}/(i lam L) ∫ E(x) exp(i π |x' - x|² / (lam L)) dx` with `k = 2π / lam`
(J. W. Goodman, *Introduction to Fourier Optics*, eq. (4-17)), whose far-field limit is the
Fraunhofer formula used by the paper. -/
def fresnelField (lam L : ℝ) (E : Plane → ℂ) (x' : Plane) : ℂ :=
  Complex.exp (((2 * Real.pi * L / lam : ℝ) : ℂ) * Complex.I) / (Complex.I * ((lam * L : ℝ) : ℂ)) *
    ∫ x : Plane, Complex.exp (((Real.pi * ‖x' - x‖ ^ 2 / (lam * L) : ℝ) : ℂ) * Complex.I) * E x

/-- Main text, p. 2 ("a thin diffuser that can be modeled as a random phase mask"): the field on
the far side of an infinitely thin second layer, `e^{i φ(x')} E(x')`, for one realization
`φ` of the random phase of the mask. -/
def phaseMaskField (φ : Plane → ℝ) (E : Plane → ℂ) (x' : Plane) : ℂ :=
  Complex.exp ((φ x' : ℂ) * Complex.I) * E x'

/-- Eq. (1), p. 2: the light intensity `I_camera(x', y')` on the external facet of the second layer,
as imaged by the camera, when the object field `E` has propagated a distance `L` at wavelength `lam`
and passed the thin phase mask `φ`. -/
def cameraIntensity (lam L : ℝ) (φ : Plane → ℝ) (E : Plane → ℂ) (x' : Plane) : ℝ :=
  ‖phaseMaskField φ (fresnelField lam L E) x'‖ ^ 2

/-- Eq. (1), p. 2: the power spectrum `|F(E)(u)|²` of a field `E`, with `F` the Fourier transform
`F(E)(u) = ∫ E(x) e^{-2π i ⟨x, u⟩} dx`. -/
def powerSpectrum (E : Plane → ℂ) (u : Plane) : ℝ :=
  ‖𝓕 E u‖ ^ 2

/-- Eq. (2), p. 2: the field autocorrelation `A = E ⋆ E`,
`A(x) = ∫ conj(E(y)) E(x + y) dy`. -/
def autocorrelation (E : Plane → ℂ) (x : Plane) : ℂ :=
  ∫ y : Plane, (starRingEnd ℂ) (E y) * E (x + y)

end Arxiv1808_03267


