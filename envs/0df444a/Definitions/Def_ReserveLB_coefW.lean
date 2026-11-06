-- Prove2me | Definitions.Def_ReserveLB_coefW
-- name    : ReserveLB_coefW
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:32:55.967206+00:00
-- url     : https://prove2.me/theorems/36148e97-74f4-4e17-92a2-ca86f937617b
-- title:
--   Prefix-risk coefficient $w_{jqrh}$ (true value)
-- statement:
--   For a pattern $q$, a singleton class $h$ ($q_h = 1$) and a class $r$ with $g(q, h) \le r < h$ (every $r < h$ when $h = f(q)$),
--   $$
--   w_{jqrh} = \beta_{\lambda_{rh}}\!\Bigl(\frac{Y_{jqh}}{3 T S_h}\Bigr),\qquad \lambda_{rh} = \lfloor P_h / A_r \rfloor,
--   $$
--   and $w_{jqrh} = 0$ otherwise. The prefix-risk rows of (4) use rational lower enclosures $\underline w_{jqrh}$ of these values.
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Section 3, p.5

import Mathlib
import Definitions.Def_ReserveLB_ClassStr
import Definitions.Def_ReserveLB_effSizeLaw
import Definitions.Def_ReserveLB_portionY
import Definitions.Def_ReserveLB_prevActive
import Definitions.Def_ReserveLB_lam

namespace ReserveLB

/-- **Prefix-risk coefficient `w_jqrh` (true value).**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Section 3, p.5: "For singleton h, g(q, h) ≤ r < h, use wjqrh = βλrh(Yjqh/(3TSh)),
λrh = ⌊Ph/Ar⌋ ≥ 1. For a first singleton use every r < h; other risk coefficients are zero."

For the law `μ` of `X_j`: if `q_h = 1`, `r < h`, and `g(q, h) ≤ r` (no condition when `h` has no
earlier active class, i.e. `h = f(q)`), then `coefW C T μ q r h = β_(λ_rh)(Y_jqh / (3 T S_h))`;
otherwise `0`.

**Formalization Note.** This is the true coefficient; (4) uses a lower enclosure of it. -/
noncomputable def coefW (C : ClassStr) (T : ℝ) (μ : List (ℚ × ℚ)) (q : Fin C.L → Fin 3)
    (r h : Fin C.L) : ℝ :=
  if q h = 1 ∧ r < h ∧ (prevActive q h).all (fun g => decide (g ≤ r)) = true then
    effSizeLaw μ (lam C r h) (fun x => portionY C.S T q h x / (3 * T * C.S h))
  else 0

end ReserveLB


