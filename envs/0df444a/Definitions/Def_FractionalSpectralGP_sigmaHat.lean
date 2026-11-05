-- Prove2me | Definitions.Def_FractionalSpectralGP_sigmaHat
-- name    : FractionalSpectralGP_sigmaHat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:22:55.092722+00:00
-- url     : https://prove2.me/theorems/951b928c-c14b-4dc5-a0bd-24601e503629
-- title:
--   Fourier transform of a measure, $\widehat\sigma(t)=\int e^{itu}\,d\sigma(u)$
-- statement:
--   For a Borel measure $\sigma$ on $\mathbb R$, its Fourier transform is
--
--   $$
--   \widehat\sigma(t)=\int_{\mathbb R}e^{itu}\,d\sigma(u),\qquad t\in\mathbb R .
--   $$
--
--   It enters the spectral-pair criterion (3.1), the expansion (5.2) of $Q_\sigma\psi$, and the coefficients of the processes $X_\sigma$ and $W_\sigma$ in (6.2) and (6.4).
--
--   **Formalization Note** Plus sign and no $2\pi$, as in the paper. For a finite measure the integrand is bounded and continuous, so the value is never a junk default.
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, §3, p.8; (3.1), (5.2), (6.2), (6.4)

import Mathlib

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- The Fourier transform of a measure on the line, `σ̂(t) = ∫_ℝ e^{itu} dσ(u)`
(Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, §3, p.8; (3.1), (5.2), (6.2), (6.4)).

**Formalization Note.** Plus sign, no `2π`. For a finite measure the integrand is bounded and
continuous, so the integral is never a junk value. -/
noncomputable def sigmaHat (σ : Measure ℝ) (t : ℝ) : ℂ :=
  ∫ u, Complex.exp (Complex.I * (t * u)) ∂σ

end FractionalSpectralGP


