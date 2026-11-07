-- Prove2me | Definitions.Def_OptimalSpectrum_Entangled_phiPoly
-- name    : OptimalSpectrum_Entangled_phiPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:16.98091+00:00
-- url     : https://prove2.me/theorems/0f853a25-29ba-4b6f-afd0-05bd15fc171c
-- title:
--   Full-interval Chebyshev basis $\phi_k(x)=T_k\big(\tfrac{x-L/2}{L/2}\big)-(-1)^k$
-- statement:
--   For $L>0$ and $k\ge1$,
--
--   $$\phi_k(x)=T_k\Big(\frac{x-L/2}{L/2}\Big)-(-1)^k,$$
--
--   where $T_k$ is the degree-$k$ Chebyshev polynomial of the first kind ($T_0=1$, $T_1=x$, $T_k=2xT_{k-1}-T_{k-2}$). The affine map sends $[0,L]$ onto $[-1,1]$, and $\phi_k(0)=0$. Moment matching in this basis gives the recovery bound of Proposition 6.1.
-- source:
--   Bakshi, Singh, Tan, Optimal spectrum estimation, arXiv:2609.30171, Proposition 6.1, Eq. (20), p. 14 (PDF p. 16)

import Mathlib

namespace OptimalSpectrum.Entangled

/-- **Full-interval Chebyshev basis `ϕ_k`.**
Bakshi, Singh, Tan, *Optimal spectrum estimation*, arXiv:2609.30171, Proposition 6.1, Eq. (20), printed p. 14 (PDF p. 16): "For 1 ⩽ k ⩽ K, define
ϕ_k(x) := T_k((x − L/2)/(L/2)) − (−1)^k."

`phiPoly L k` is the real polynomial `x ↦ T_k((x − L/2)/(L/2)) − (−1)^k`, where `T_k` is the
degree-`k` Chebyshev polynomial of the first kind (Definition 4.4, printed p. 12). It maps
`[0, L]` affinely onto `[−1, 1]` and satisfies `ϕ_k(0) = 0`.

**Formalization Note.** `T_k` is Mathlib's `Polynomial.Chebyshev.T ℝ k` (integer index, here a
natural `k`), which satisfies the recursion of Definition 4.4. -/
noncomputable def phiPoly (L : ℝ) (k : ℕ) : Polynomial ℝ :=
  (Polynomial.Chebyshev.T ℝ (k : ℤ)).comp
      (Polynomial.C (L / 2)⁻¹ * (Polynomial.X - Polynomial.C (L / 2))) -
    Polynomial.C ((-1 : ℝ) ^ k)

end OptimalSpectrum.Entangled


