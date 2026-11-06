-- Prove2me | Definitions.Def_GeomDRSub_hAct
-- name    : GeomDRSub_hAct
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:11:12.824717+00:00
-- url     : https://prove2.me/theorems/baaa96cb-9f57-4aed-b531-f378553acdf0
-- title:
--   The action map $h_\zeta$
-- statement:
--   The **action map** sends a state $x$ to the point $h_\zeta(x)$ with coordinates
--   $$
--   [h_\zeta(x)]_i=\frac{x_i}{c_\zeta+x_i}\qquad(i\in[d]).
--   $$
--   On the cube the denominators are at least $1/2$, and $0\le [h_\zeta(x)]_i\le 1/(1+c_\zeta)<1$. The online algorithm keeps a state $x_t$ and plays $p_t=h_\zeta(x_t)$.
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Section 4.1, p.10, Eq. (11)

import Mathlib
import Definitions.Def_GeomDRSub_cZeta

namespace GeomDRSub

/-- **The action map `h_ζ`** of Eq. (11). Aggarwal–Lu, arXiv:2610.00545, Section 4.1, p.10:
`[h_ζ(x)]ᵢ = xᵢ/(c_ζ + xᵢ)`.

**Formalization Note.** The formula is applied coordinatewise to every vector; it is used on
states `x` in the cube, where `c_ζ + xᵢ ≥ 1/2 > 0`. -/
noncomputable def hAct {d : ℕ} (ζ : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => x i / (cZeta ζ + x i))

end GeomDRSub


