-- Prove2me | Definitions.Def_ReserveLB_wExact
-- name    : ReserveLB_wExact
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:34:07.100489+00:00
-- url     : https://prove2.me/theorems/214a4d5b-6c1d-4b1a-a147-3deeba5cb3a8
-- title:
--   Exact case of a prefix-risk coefficient
-- statement:
--   A prefix-risk coefficient $w_{jqrh}$ is in the **exact case** if its base is one ($\lambda_{rh} = 1$) or it is zero.
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Section 3, p.5

import Mathlib
import Definitions.Def_ReserveLB_ClassStr
import Definitions.Def_ReserveLB_coefW
import Definitions.Def_ReserveLB_lam

namespace ReserveLB

/-- **Exact prefix-risk case.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Section 3, p.5: "Base-one and zero cases are exact".

`wExact C T μ q r h` holds when the prefix-risk coefficient has base one (`λ_rh = 1`) or is zero.

**Formalization Note.** Used by `IsLowerEnclosure` and by (7). -/
def wExact (C : ClassStr) (T : ℝ) (μ : List (ℚ × ℚ)) (q : Fin C.L → Fin 3) (r h : Fin C.L) :
    Prop :=
  lam C r h = 1 ∨ coefW C T μ q r h = 0

end ReserveLB


