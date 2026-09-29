-- Prove2me | Definitions.Def_DeBruijnNewman_Dobner
-- name    : DeBruijnNewman_Dobner
-- status  : Definition
-- author  : @adobner
-- created : 2026-09-24T21:39:53.61331+00:00
-- url     : https://prove2.me/theorems/4ed13730-f6ea-4874-a400-a195ad1fe3c6
-- title:
--   Auxiliary functions for Dobner's proof of Newman's conjecture
-- statement:
--   These definitions specialize the auxiliary functions in Dobner's proof to the Riemann zeta function. For real time $t$ and complex $s$, put
--
--   $$
--   Z_t(s)=\sum_{n=1}^{\infty}\exp\!\left(\frac{t}{4}\log^2n\right)n^{-s},
--   \qquad
--   J_t(s)=s+\frac{|t|}{4}\Log\!\left(\frac{s}{2\pi}\right).
--   $$
--
--   The intended analytic regime is $t<0$, in which the series is everywhere absolutely convergent. Convergence is not assumed in these definitions. Define
--
--   $$
--   \gamma(s)=\frac{s(s-1)}{2}\exp\!\left(-\frac{s}{2}\log\pi\right)\Gamma(s/2),
--   \qquad
--   \gamma_t(s)=\gamma(s)\exp\!\left(\frac{(s-J_t(s))^2}{|t|}\right).
--   $$
--
--   Using the existing platform heat flow, set
--
--   $$
--   \xi_t(s)=8H_t\bigl(-i(2s-1)\bigr),
--   \qquad
--   h_t(s)=\frac{\xi_t(J_t(s))}{\gamma_t(s)}.
--   $$
--
--   The factor eight accounts for the paper's kernel being four times the platform's kernel and the passage from the full Fourier integral to the half-line cosine integral. The time parameter is unchanged. These functions make the paper's Dirichlet-series approximation directly applicable to the canonical heat flow.
--
--   **Formalization Note** The Dirichlet series is a `tsum` over natural numbers with the index shifted by one; each summand is represented as a complex exponential. `Complex.log` is the principal logarithm. The definitions are total, using Mathlib's conventions for sums and division, while the subsequent analytic statements explicitly restrict to negative time and the upper half-plane.
-- source:
--   Alexander Dobner, A proof of Newman's conjecture for the extended Selberg class, arXiv:2005.05142v2 (10 January 2026), https://arxiv.org/abs/2005.05142v2, Introduction pp. 2–4; Theorem 4, definitions (11)–(13), p. 13; Section 3.1, pp. 14–15. Zeta specialization and normalization to the existing DeBruijnNewman_core.

import Definitions.Def_DeBruijnNewman_core

/-!
The auxiliary functions from Alexander Dobner,
`A proof of Newman's conjecture for the extended Selberg class`,
arXiv:2005.05142, specialized to the Riemann zeta function.

The paper's Fourier kernel is four times `DeBruijnNewman.Phi`; evenness
introduces another factor of two. Thus its xi deformation in s coordinates
is `8 * H t (-I * (2 * s - 1))`, with exactly the same time parameter.
-/

namespace DeBruijnNewman.Dobner

/-- The everywhere convergent Dirichlet series of the paper, for `t < 0`.
The summation variable represents the positive integer `n + 1`. -/
noncomputable def zetaT (t : ℝ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, Complex.exp
    (((t / 4 * Real.log ((n : ℝ) + 1) ^ 2 : ℝ) : ℂ)
      - s * (Real.log ((n : ℝ) + 1) : ℂ))

/-- The change of coordinates from the introduction and Theorem 4. -/
noncomputable def J (t : ℝ) (s : ℂ) : ℂ :=
  s + ((|t| / 4 : ℝ) : ℂ) * Complex.log (s / ((2 * Real.pi : ℝ) : ℂ))

/-- The factor multiplying zeta in the completed Riemann xi function. -/
noncomputable def gammaFactor (s : ℂ) : ℂ :=
  s * (s - 1) / 2 * Complex.exp (-(s / 2) * (Real.log Real.pi : ℂ))
    * Complex.Gamma (s / 2)

/-- The modified gamma factor in Theorem 4. -/
noncomputable def gammaT (t : ℝ) (s : ℂ) : ℂ :=
  gammaFactor s * Complex.exp ((s - J t s) ^ 2 / ((|t| : ℝ) : ℂ))

/-- The paper's deformed xi function, with the platform's normalization. -/
noncomputable def xiT (t : ℝ) (s : ℂ) : ℂ :=
  8 * H t (-Complex.I * (2 * s - 1))

/-- The holomorphic normalized function used in Section 3.1. -/
noncomputable def normalizedXi (t : ℝ) (s : ℂ) : ℂ :=
  xiT t (J t s) / gammaT t s

end DeBruijnNewman.Dobner


