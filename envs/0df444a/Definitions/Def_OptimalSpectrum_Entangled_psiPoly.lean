-- Prove2me | Definitions.Def_OptimalSpectrum_Entangled_psiPoly
-- name    : OptimalSpectrum_Entangled_psiPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:19.486357+00:00
-- url     : https://prove2.me/theorems/3afe01c6-ec15-4221-b522-6b62f5921dd3
-- title:
--   Interior Chebyshev basis $\psi_k(x)=T_k\big(\tfrac{x-L/2}{L}\big)-T_k(-1/2)$
-- statement:
--   For $L>0$ and $k\ge1$,
--
--   $$\psi_k(x)=T_k\Big(\frac{x-L/2}{L}\Big)-T_k(-1/2).$$
--
--   The affine map sends $[0,L]$ onto $[-1/2,1/2]$, the interior of the Chebyshev interval, and $\psi_k(0)=0$. Its derivatives are smaller than those of $\phi_k$, which is what Proposition 6.2 trades against a weaker approximation bound.
-- source:
--   Bakshi, Singh, Tan, Optimal spectrum estimation, arXiv:2609.30171, Proposition 6.2, Eq. (22), p. 14 (PDF p. 16)

import Mathlib

namespace OptimalSpectrum.Entangled

/-- **Interior Chebyshev basis `ψ_k`.**
Bakshi, Singh, Tan, *Optimal spectrum estimation*, arXiv:2609.30171, Proposition 6.2, Eq. (22), printed p. 14 (PDF p. 16): "For 1 ⩽ k ⩽ K, define
ψ_k(x) := T_k((x − L/2)/L) − T_k(−1/2)."

`psiPoly L k` is the real polynomial `x ↦ T_k((x − L/2)/L) − T_k(−1/2)`. It maps `[0, L]` affinely
onto `[−1/2, 1/2]` and satisfies `ψ_k(0) = 0`.

**Formalization Note.** `T_k` is Mathlib's `Polynomial.Chebyshev.T ℝ k`. -/
noncomputable def psiPoly (L : ℝ) (k : ℕ) : Polynomial ℝ :=
  (Polynomial.Chebyshev.T ℝ (k : ℤ)).comp
      (Polynomial.C L⁻¹ * (Polynomial.X - Polynomial.C (L / 2))) -
    Polynomial.C ((Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (-1 / 2))

end OptimalSpectrum.Entangled


