-- Prove2me | Definitions.Def_GeomDRSub_Supplement_Q0
-- name    : GeomDRSub_Supplement_Q0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:48:32.17136+00:00
-- url     : https://prove2.me/theorems/09ba649b-74bf-4a8e-9f5e-08f0e65865af
-- title:
--   The quadratic $Q_{0,n,\zeta}(x;\omega)$
-- statement:
--   For weights $\omega=(\eta,\theta,\lambda,\mu)$ and $N=2n$,
--   $$Q_{0,n,\zeta}(x;\omega)=\eta\Big(\tfrac12-2x^2\Big)+\theta(1+N\xi_{n,\zeta}x)+\mu(1+2x)(\chi_n+\ell_n\xi_{n,\zeta}x)$$
--   (Eq. (150)). It bounds the four-component objective at symmetric points with $s=0$.
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Section 6.2, p.38, Eq. (150)

import Mathlib
import Definitions.Def_GeomDRSub_Supplement_rN
import Definitions.Def_GeomDRSub_Supplement_xiN
import Definitions.Def_GeomDRSub_Supplement_chiN
import Definitions.Def_GeomDRSub_Supplement_ellN

namespace GeomDRSub.Supplement

/-- **The quadratic `Q_{0,n,ζ}(x; ω)`**, Eq. (150). Aggarwal–Lu, *Geometry-Dependent Online and Offline Approximation for Non-Monotone
DR-Submodular Maximization*, arXiv:2610.00545, Section 6.2, p.38:
`Q_{0,n,ζ}(x; ω) = η(1/2 − 2x²) + θ(1 + Nξ_{n,ζ}x) + µ(1 + 2x)(χ_n + ℓ_nξ_{n,ζ}x)`.

**Formalization Note.** The weights `ω = (η, θ, λ, μ)` are `w 0, w 1, w 2, w 3`; `N = 2n`. -/
noncomputable def Q0 (n : ℕ) (ζ : ℝ) (w : Fin 4 → ℝ) (x : ℝ) : ℝ :=
  w 0 * (1 / 2 - 2 * x ^ 2) + w 1 * (1 + 2 * n * xiN n ζ * x) +
    w 3 * ((1 + 2 * x) * (chiN n + ellN n * xiN n ζ * x))

end GeomDRSub.Supplement


