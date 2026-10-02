-- Prove2me | Definitions.Def_TeschlQM_Dynamics_measureFourier
-- name    : TeschlQM_Dynamics_measureFourier
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T06:49:04.253351+00:00
-- url     : https://prove2.me/theorems/4c3a12f8-c289-4f48-b006-244e5bde08e7
-- title:
--   Fourier transform μ̂(t) of a finite complex Borel measure (5.8)
-- statement:
--   Let $\mu$ be a finite complex Borel measure on $\mathbb R$. Its **Fourier transform** is
--   $$\hat\mu(t) = \int_{\mathbb R} \mathrm e^{-\mathrm it\lambda}\, d\mu(\lambda), \qquad t \in \mathbb R .$$
--   For the spectral measures of a self-adjoint operator, $\hat\mu_{\varphi,\psi}(t) = \langle\varphi, \mathrm e^{-\mathrm itA}\psi\rangle$.
--
--   **Formalization Note.** $\mu$ is a `ComplexMeasure ℝ` (a countably additive $\mathbb C$-valued function on Borel sets, hence of finite total variation). The integral is Mathlib's integral against a vector measure, `VectorMeasure.integral`, with the pairing given by multiplication in $\mathbb C$; the integrand is bounded and continuous, so it is integrable against the total variation of $\mu$. The normalization is the book's: no factor $2\pi$ and no prefactor.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 126, Section 5.2, Eq. (5.8)

import Mathlib

open MeasureTheory

namespace TeschlQM.Dynamics

/-- Teschl, p. 126, (5.8): the **Fourier transform** `μ̂(t) = ∫_ℝ e^{−itλ} dμ(λ)` of a finite
complex Borel measure `μ` on `ℝ` (a `ComplexMeasure ℝ`, i.e. a countably additive `ℂ`-valued
set function on the Borel sets, which is automatically finite). The integral is Mathlib's
integral against a vector measure (`VectorMeasure.integral`) with the pairing given by complex
multiplication; the integrand is bounded and continuous, hence integrable with respect to the
total variation of `μ`. -/
noncomputable def measureFourier (μ : ComplexMeasure ℝ) (t : ℝ) : ℂ :=
  μ.integral (fun x : ℝ => Complex.exp (-(Complex.I * (t : ℂ) * (x : ℂ))))
    (ContinuousLinearMap.mul ℝ ℂ)

end TeschlQM.Dynamics


