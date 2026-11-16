-- Prove2me | Definitions.Def_GeomDRSub_Supplement_U
-- name    : GeomDRSub_Supplement_U
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:50:27.641582+00:00
-- url     : https://prove2.me/theorems/76191dfa-62d2-4198-a5a6-3b20b761d862
-- title:
--   The four-component upper function $U(\zeta)$
-- statement:
--   $$U(\zeta)=\inf_{n\ge2}V_n(\zeta)\quad(0\le\zeta<1/2),\qquad U(\zeta)=\tfrac12\quad(1/2\le\zeta\le1)$$
--   (Eq. (151)).
--
--   **Formalization Note** The infimum is over a nonempty set of reals bounded below by $0$.
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Section 6.2, p.38, Eq. (151)

import Mathlib
import Definitions.Def_GeomDRSub_Supplement_Vn

namespace GeomDRSub.Supplement

/-- **The four-component upper function `U(ζ)`**, Eq. (151). Aggarwal–Lu, *Geometry-Dependent Online and Offline Approximation for Non-Monotone
DR-Submodular Maximization*, arXiv:2610.00545, Section 6.2, p.38:
`U(ζ) = inf_{n≥2} V_n(ζ)` for `0 ≤ ζ < 1/2`, and `U(ζ) = 1/2` for `1/2 ≤ ζ ≤ 1`.

**Formalization Note.** The infimum is `sInf` of `{V_n(ζ) : n ≥ 2}`, a nonempty set bounded below
by `0` (each `Q_{j,n,ζ}(0; ω) ≥ 0` on `Δ₄`). Only `ζ ∈ [0,1]` is used. -/
noncomputable def U (ζ : ℝ) : ℝ :=
  if ζ < 1 / 2 then sInf ((fun n : ℕ => Vn n ζ) '' {n : ℕ | 2 ≤ n}) else 1 / 2

end GeomDRSub.Supplement


