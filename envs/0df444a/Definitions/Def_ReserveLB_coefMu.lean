-- Prove2me | Definitions.Def_ReserveLB_coefMu
-- name    : ReserveLB_coefMu
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:30:55.953047+00:00
-- url     : https://prove2.me/theorems/72b9267a-f0ca-46fe-a3d4-a07b63516a28
-- title:
--   Mean coefficient $\mu_{jqh}$
-- statement:
--   For a pattern $q$ and an active class $h$,
--   $$
--   \mu_{jqh} = \frac{\mathbb E\, Y_{jqh}}{T S_h},
--   $$
--   and $\mu_{jqh} = 0$ for an inactive class. The mean rows of (4) use these exact coefficients.
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Section 3, p.5

import Mathlib
import Definitions.Def_ReserveLB_ClassStr
import Definitions.Def_ReserveLB_lawExpect
import Definitions.Def_ReserveLB_portionY

namespace ReserveLB

/-- **Mean coefficient `µ_jqh`.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Section 3, p.5: "Put µjqh = EYjqh/(TSh)".

For the law `μ` of `X_j`, `coefMu C T μ q h = E Y_jqh / (T S_h)` for active `h`, and `0` for
inactive `h`.

**Formalization Note.** Exact (no enclosure), as in (4). -/
noncomputable def coefMu (C : ClassStr) (T : ℝ) (μ : List (ℚ × ℚ)) (q : Fin C.L → Fin 3)
    (h : Fin C.L) : ℝ :=
  if q h ≠ 0 then lawExpect μ (portionY C.S T q h) / (T * C.S h) else 0

end ReserveLB


