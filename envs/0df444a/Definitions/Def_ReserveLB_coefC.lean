-- Prove2me | Definitions.Def_ReserveLB_coefC
-- name    : ReserveLB_coefC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:30:56.531217+00:00
-- url     : https://prove2.me/theorems/287843d7-aeda-48d7-84ea-25100c7a37b2
-- title:
--   Exception coefficient $c_{jq}$
-- statement:
--   For a pattern $q$,
--   $$
--   c_{jq} = \frac{\mathbb E\, E_{jq}}{T S_{f(q)}} .
--   $$
--   The exception row of (4) uses these exact coefficients.
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Section 3, p.5

import Mathlib
import Definitions.Def_ReserveLB_ClassStr
import Definitions.Def_ReserveLB_lawExpect
import Definitions.Def_ReserveLB_portionE
import Definitions.Def_ReserveLB_firstActive

namespace ReserveLB

/-- **Exception coefficient `c_jq`.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Section 3, p.5: "cjq = EEjq/(TSf(q))".

For the law `μ` of `X_j`, `coefC C T μ q = E E_jq / (T S_(f(q)))`.

**Formalization Note.** Exact, as in (4). The value `0` without an active class is never used. -/
noncomputable def coefC (C : ClassStr) (T : ℝ) (μ : List (ℚ × ℚ)) (q : Fin C.L → Fin 3) : ℝ :=
  match firstActive q with
  | some f => lawExpect μ (portionE C.S T q) / (T * C.S f)
  | none => 0

end ReserveLB


