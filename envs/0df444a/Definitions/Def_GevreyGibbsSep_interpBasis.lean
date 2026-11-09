-- Prove2me | Definitions.Def_GevreyGibbsSep_interpBasis
-- name    : GevreyGibbsSep_interpBasis
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:36:43.873194+00:00
-- url     : https://prove2.me/theorems/d718efd7-d28d-4dc2-9895-4e284d51bf6a
-- title:
--   Fourier interpolation basis $\psi_{k_1}(x_1)\cdots\psi_{k_d}(x_d)$
-- statement:
--   For $k=-N,\dots,N$ let
--   $$\psi_k(x)=\frac{1}{\sqrt{2\pi(2N+1)}}\sum_{j=-N}^{N}e^{ij(x-x_k)},\qquad x_k=\frac{2\pi k}{2N+1}.$$
--   This item is the product $\psi_{k_1}(x_1)\cdots\psi_{k_d}(x_d)$; the interpolation isometry is $I_N|u\rangle=\sum_k u(k)\,\psi_{k_1}(x_1)\cdots\psi_{k_d}(x_d)$ (A13).
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Eqs. (A12)–(A13), pp.21–22

import Mathlib
import Definitions.Def_GevreyGibbsSep_Grid
import Definitions.Def_GevreyGibbsSep_gridPt

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- The interpolation basis function `ψ_{k₁}(x₁) ⋯ ψ_{k_d}(x_d)` with
`ψ_k(x) = (2π(2N + 1))^{−1/2} ∑_{j=−N}^{N} e^{ij(x − x_k)}` (arXiv:2608.24527 (sha256 d4fd40eb…),
Eqs. (A12)–(A13), pp.21–22); `I_N |u⟩ = ∑_k u(k) ψ_{k₁}(x₁) ⋯ ψ_{k_d}(x_d)`. -/
noncomputable def interpBasis (d N : ℕ) (k : Grid d N) (x : Fin d → ℝ) : ℂ :=
  ∏ i, (((Real.sqrt (2 * Real.pi * (2 * N + 1)))⁻¹ : ℝ) : ℂ) *
    ∑ j : Fin (2 * N + 1), Complex.exp (Complex.I * ((((j : ℕ) : ℝ) - N : ℝ) : ℂ) *
      ((x i - gridPt d N k i : ℝ) : ℂ))

end GevreyGibbsSep


