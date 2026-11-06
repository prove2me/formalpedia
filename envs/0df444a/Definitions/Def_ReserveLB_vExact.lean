-- Prove2me | Definitions.Def_ReserveLB_vExact
-- name    : ReserveLB_vExact
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:32:03.297186+00:00
-- url     : https://prove2.me/theorems/e14fd979-1afe-49d5-82a8-e2efa934f1ac
-- title:
--   Exact case of a first-risk coefficient
-- statement:
--   A first-risk coefficient $v_{jq}$ is in the **exact case** if its base is one ($N_{f(q)} = 1$) or it is zero; then its enclosure is the coefficient itself.
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Section 3, p.5

import Mathlib
import Definitions.Def_ReserveLB_ClassStr
import Definitions.Def_ReserveLB_coefV
import Definitions.Def_ReserveLB_firstActive

namespace ReserveLB

/-- **Exact first-risk case.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Section 3, p.5: "Base-one and zero cases are exact".

`vExact C T μ q` holds when the first-risk coefficient has base one (`N_(f(q)) = 1`) or is zero; its
lower enclosure is then the coefficient itself.

**Formalization Note.** Used by `IsLowerEnclosure` and by (7). -/
def vExact (C : ClassStr) (T : ℝ) (μ : List (ℚ × ℚ)) (q : Fin C.L → Fin 3) : Prop :=
  (∃ f, firstActive q = some f ∧ C.N f = 1) ∨ coefV C T μ q = 0

end ReserveLB


