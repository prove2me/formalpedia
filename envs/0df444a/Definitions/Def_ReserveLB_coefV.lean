-- Prove2me | Definitions.Def_ReserveLB_coefV
-- name    : ReserveLB_coefV
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:30:58.971267+00:00
-- url     : https://prove2.me/theorems/7054a499-e347-424b-be7a-f37527dbfbf8
-- title:
--   First-risk coefficient $v_{jq}$ (true value)
-- statement:
--   For a pattern $q$ whose first active class $f = f(q)$ is a singleton ($q_f = 1$),
--   $$
--   v_{jq} = \beta_{N_f}\!\Bigl(\frac{Y_{jqf}}{3 T S_f}\Bigr),
--   $$
--   and $v_{jq} = 0$ otherwise. The first-risk rows of (4) use rational lower enclosures $\underline v_{jq}$ of these values.
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Section 3, p.5

import Mathlib
import Definitions.Def_ReserveLB_ClassStr
import Definitions.Def_ReserveLB_effSizeLaw
import Definitions.Def_ReserveLB_portionY
import Definitions.Def_ReserveLB_firstActive

namespace ReserveLB

/-- **First-risk coefficient `v_jq` (true value).**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Section 3, p.5: "For a first singleton use vjq = βNf(q)(Yjq,f(q)/(3TSf(q)))"; "other
risk coefficients are zero".

For the law `μ` of `X_j`, with `f = f(q)`: if `q_f = 1`, `coefV C T μ q = β_(N_f)(Y_jqf / (3 T S_f))`;
otherwise `0`.

**Formalization Note.** This is the true coefficient; (4) uses a lower enclosure of it
(`IsLowerEnclosure`). -/
noncomputable def coefV (C : ClassStr) (T : ℝ) (μ : List (ℚ × ℚ)) (q : Fin C.L → Fin 3) : ℝ :=
  match firstActive q with
  | some f =>
      if q f = 1 then effSizeLaw μ (C.N f) (fun x => portionY C.S T q f x / (3 * T * C.S f))
      else 0
  | none => 0

end ReserveLB


