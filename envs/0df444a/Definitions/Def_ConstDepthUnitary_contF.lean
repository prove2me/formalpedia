-- Prove2me | Definitions.Def_ConstDepthUnitary_contF
-- name    : ConstDepthUnitary_contF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:43:30.116632+00:00
-- url     : https://prove2.me/theorems/4a7d919a-94e3-4245-8d99-ab0ddf4cf6d9
-- title:
--   The continuous Fourier transform $F$
-- statement:
--   The Fourier transform without the factor $2\pi$ in the exponent, on functions $\psi:\mathbb R^N\to\mathbb C$:
--   $$(F\psi)(v)=\frac1{(2\pi)^{N/2}}\int_{\mathbb R^N}e^{-iu^{\mathsf T}v}\psi(u)\,du.$$
--
--   **Formalization Note** The Bochner integral of a non-integrable function is $0$. Every statement of the mission applies $F$ to a Schwartz function only, for which the integrand is integrable.
-- source:
--   Nehoran, Slote, Yuen, All Unitaries Have Constant Depth Quantum Circuits, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), §3.3, p.17; Eq. (27)

import Mathlib
open scoped RealInnerProductSpace

namespace ConstDepthUnitary

/-- The continuous Fourier transform `(F ψ)(v) = (2π)^{−N/2} ∫ e^{−i uᵀv} ψ(u) du` on `ℝ^N`.

Nehoran, Slote, Yuen, *All Unitaries Have Constant Depth Quantum Circuits*, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Lemma 3.2, p.17; Eq. (27).

**Formalization Note** The Bochner integral is `0` on a non-integrable integrand; every statement of the
mission applies `contF` to a Schwartz function only, so the integrand is integrable. -/
noncomputable def contF {N : ℕ} (ψ : EuclideanSpace ℝ (Fin N) → ℂ) (v : EuclideanSpace ℝ (Fin N)) : ℂ :=
  (((2 * Real.pi) ^ (-(N : ℝ) / 2) : ℝ) : ℂ) *
    ∫ u : EuclideanSpace ℝ (Fin N), Complex.exp (-Complex.I * ((⟪u, v⟫ : ℝ) : ℂ)) * ψ u

end ConstDepthUnitary


