-- Prove2me | Definitions.Def_OptimalSpectrum_Entangled_chebCoeff
-- name    : OptimalSpectrum_Entangled_chebCoeff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:26.051869+00:00
-- url     : https://prove2.me/theorems/7cac6e58-e079-4c07-a5c2-179ad2df1955
-- title:
--   Chebyshev coefficients $\gamma_k$ of a function on $[-1,1]$
-- statement:
--   For a function $f$ on $[-1,1]$, its Chebyshev expansion $f(t)=\gamma_0+\sum_{k\ge1}\gamma_kT_k(t)$ has coefficients
--
--   $$\gamma_0=\frac1\pi\int_{-1}^1\frac{f(t)}{\sqrt{1-t^2}}\,dt,\qquad \gamma_k=\frac2\pi\int_{-1}^1\frac{f(t)\,T_k(t)}{\sqrt{1-t^2}}\,dt\quad(k\ge1),$$
--
--   the orthogonal projection coefficients for the weight $1/\sqrt{1-t^2}$ (Fact 4.5). Lemma 6.3 damps these coefficients to build polynomial approximations.
--
--   **Formalization Note** No convergence of the series is asserted; only the coefficients are defined.
-- source:
--   Bakshi, Singh, Tan, Optimal spectrum estimation, arXiv:2609.30171, Lemma 6.3, p. 15 (PDF p. 17)

import Mathlib

namespace OptimalSpectrum.Entangled

/-- **Chebyshev coefficients `γ_k` of a function on `[−1, 1]`.**
Bakshi, Singh, Tan, *Optimal spectrum estimation*, arXiv:2609.30171, Lemma 6.3, printed p. 15 (PDF p. 17): "Write the Chebyshev expansion of f as
f(t) = γ₀ + ∑_(k⩾1) γ_k T_k(t)."

The coefficients of the Chebyshev expansion are
`γ₀ = (1/π) ∫_(−1)^1 f(t) dt/√(1 − t²)` and `γ_k = (2/π) ∫_(−1)^1 f(t) T_k(t) dt/√(1 − t²)` for
`k ≥ 1`, the orthogonal-projection coefficients for the weight `1/√(1 − t²)` (Fact 4.5).

**Formalization Note.** The integral is over `(−1, 1)`; the weight is integrable there, so for a
continuous `f` on `[−1, 1]` the integral is an honest Lebesgue integral (the value `1/0 = 0` of the
weight at the two endpoints is on a null set). Convergence of the series is not asserted. -/
noncomputable def chebCoeff (f : ℝ → ℝ) (k : ℕ) : ℝ :=
  (if k = 0 then 1 / Real.pi else 2 / Real.pi) *
    ∫ t in (-1 : ℝ)..1, f t * (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval t / Real.sqrt (1 - t ^ 2)

end OptimalSpectrum.Entangled


