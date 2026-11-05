-- Prove2me | Definitions.Def_FractionalSpectralGP_paperFourier
-- name    : FractionalSpectralGP_paperFourier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:22:51.403747+00:00
-- url     : https://prove2.me/theorems/ec5cbd35-800d-44f4-99b9-ac3b3623738d
-- title:
--   The paper's Fourier transform $\widehat\psi(u)=\int e^{iux}\psi(x)\,dx$
-- statement:
--   For a function $\psi:\mathbb R\to\mathbb C$, the paper's Fourier transform is
--
--   $$
--   \widehat\psi(u)=\int_{\mathbb R}e^{iux}\,\psi(x)\,dx,\qquad u\in\mathbb R .
--   $$
--
--   This is the transform applied to Schwartz functions in the definition of the operator $Q_\sigma$ and in the approximation condition (5.8).
--
--   **Formalization Note** The sign in the exponent is $+$, there is no factor $2\pi$ and no normalization, so this is not Mathlib's `𝓕`. For a non-integrable $\psi$ the Bochner integral returns $0$; the mission only applies the transform to Schwartz functions.
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, p.3 (notation) and §5, p.12

import Mathlib

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- The paper's Fourier transform of a function on the line,
`ψ̂(u) = ∫_ℝ e^{iux} ψ(x) dx` (Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, §1 notation, p.3, used in §5, p.12).

**Formalization Note.** Plus sign in the exponent, no factor `2π`, no normalization: this is not
Mathlib's `𝓕` (which uses `e^{-2πi⟨x,ξ⟩}`). For a non-integrable `ψ` the Bochner integral is `0`;
in this mission it is only applied to Schwartz functions. -/
noncomputable def paperFourier (ψ : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∫ x : ℝ, Complex.exp (Complex.I * (u * x)) * ψ x

end FractionalSpectralGP


