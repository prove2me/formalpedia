-- Prove2me | Definitions.Def_GevreyGibbsSep_fourierDeriv
-- name    : GevreyGibbsSep_fourierDeriv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:36:53.600111+00:00
-- url     : https://prove2.me/theorems/4e33855d-badd-47ef-a9bc-b51510564380
-- title:
--   Approximate Fourier derivative $\tilde\partial_j$
-- statement:
--   The **approximate Fourier derivative** on the $N$-grid is
--   $$\tilde\partial_jf(x)=\sum_{\omega\in[-N,\dots,N]^d}i\omega_j\,\tilde f_\omega\,e^{i\langle\omega,x\rangle},\qquad \tilde f_\omega=\frac{1}{(2N+1)^d}\sum_{y}f(y)e^{-i\langle\omega,y\rangle},$$
--   with $x,y$ grid points. As a matrix, its entry at $(x,y)$ is $\sum_\omega i\omega_j(2N+1)^{-d}e^{i\langle\omega,x-y\rangle}$.
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Eqs. (A3), (A10), pp.20–21

import Mathlib
import Definitions.Def_GevreyGibbsSep_Grid
import Definitions.Def_GevreyGibbsSep_gridPt

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- The approximate Fourier derivative `∂̃_j` on the `N`-grid, Eq. (A10) with the discrete
Fourier coefficients (A3) (arXiv:2608.24527 (sha256 d4fd40eb…), pp.20–21):
`(∂̃_j f)(x) = ∑_{ω ∈ [−N,N]^d} i ω_j f̃_ω e^{i⟨ω,x⟩}`, `f̃_ω = (2N + 1)^{−d} ∑_y f(y) e^{−i⟨ω,y⟩}`;
as a matrix, entry `(x, y)` is `∑_ω i ω_j (2N + 1)^{−d} e^{i⟨ω, x − y⟩}`. -/
noncomputable def fourierDeriv (d N : ℕ) (j : Fin d) : Matrix (Grid d N) (Grid d N) ℂ :=
  Matrix.of fun x y => ∑ ω : Grid d N,
    Complex.I * ((((ω j : ℕ) : ℝ) - N : ℝ) : ℂ) * (((2 * N + 1 : ℝ) ^ d)⁻¹ : ℝ) *
      Complex.exp (Complex.I *
        ((∑ i, (((ω i : ℕ) : ℝ) - N) * (gridPt d N x i - gridPt d N y i) : ℝ) : ℂ))

end GevreyGibbsSep


