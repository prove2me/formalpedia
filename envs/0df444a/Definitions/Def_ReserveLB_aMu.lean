-- Prove2me | Definitions.Def_ReserveLB_aMu
-- name    : ReserveLB_aMu
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:29:24.210917+00:00
-- url     : https://prove2.me/theorems/edb9d236-421f-4313-be32-f5e06d44b9d0
-- title:
--   Mean budget $a_\mu(N)$
-- statement:
--   $$
--   a_\mu(N) = \begin{cases} 34/5, & N < 4,\\ 2 + 5/\lfloor\sqrt N\rfloor, & N \ge 4. \end{cases}
--   $$
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Section 3, p.5

import Mathlib

namespace ReserveLB

/-- **Mean budget `a_µ(N)`.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Section 3, p.5: "aµ(N) = 34/5 for N < 4, 2 + 5/⌊√N⌋ for N ≥ 4".

`aMu N = 34/5` if `N < 4`, and `2 + 5 / ⌊√N⌋` otherwise.

**Formalization Note.** `⌊√N⌋` is `Nat.sqrt N`. -/
noncomputable def aMu (N : ℕ) : ℝ :=
  if N < 4 then 34 / 5 else 2 + 5 / (Nat.sqrt N : ℝ)

end ReserveLB


