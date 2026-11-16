-- Prove2me | Definitions.Def_GeomDRSub_Supplement_Q1
-- name    : GeomDRSub_Supplement_Q1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:48:59.055198+00:00
-- url     : https://prove2.me/theorems/868027e8-0556-475e-aae6-c79bea9446b5
-- title:
--   The quadratic $Q_{1,n,\zeta}(x;\omega)$
-- statement:
--   For weights $\omega=(\eta,\theta,\lambda,\mu)$,
--   $$Q_{1,n,\zeta}(x;\omega)=\eta\Big(\tfrac12-2x^2\Big)+\theta(r_n+\xi_{n,\zeta}x)+\lambda\Big(\tfrac34+x-x^2\Big)+\mu(1+2x)(\chi_n+\ell_n\xi_{n,\zeta}x)$$
--   (Eq. (150)). It bounds the four-component objective at symmetric points with $s=1-r_n$.
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Section 6.2, p.38, Eq. (150)

import Mathlib
import Definitions.Def_GeomDRSub_Supplement_rN
import Definitions.Def_GeomDRSub_Supplement_xiN
import Definitions.Def_GeomDRSub_Supplement_chiN
import Definitions.Def_GeomDRSub_Supplement_ellN

namespace GeomDRSub.Supplement

/-- **The quadratic `Q_{1,n,ζ}(x; ω)`**, Eq. (150). Aggarwal–Lu, *Geometry-Dependent Online and Offline Approximation for Non-Monotone
DR-Submodular Maximization*, arXiv:2610.00545, Section 6.2, p.38:
`Q_{1,n,ζ}(x; ω) = η(1/2 − 2x²) + θ(r_n + ξ_{n,ζ}x) + λ(3/4 + x − x²) + µ(1 + 2x)(χ_n + ℓ_nξ_{n,ζ}x)`.

**Formalization Note.** The weights `ω = (η, θ, λ, μ)` are `w 0, w 1, w 2, w 3`; `N = 2n`. -/
noncomputable def Q1 (n : ℕ) (ζ : ℝ) (w : Fin 4 → ℝ) (x : ℝ) : ℝ :=
  w 0 * (1 / 2 - 2 * x ^ 2) + w 1 * (rN n + xiN n ζ * x) + w 2 * (3 / 4 + x - x ^ 2) +
    w 3 * ((1 + 2 * x) * (chiN n + ellN n * xiN n ζ * x))

end GeomDRSub.Supplement


