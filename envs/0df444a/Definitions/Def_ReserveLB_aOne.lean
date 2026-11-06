-- Prove2me | Definitions.Def_ReserveLB_aOne
-- name    : ReserveLB_aOne
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:29:24.990615+00:00
-- url     : https://prove2.me/theorems/7bdfa08b-7095-4b95-8ea5-7721437c69a1
-- title:
--   First-risk budget $a_1(N)$
-- statement:
--   $$
--   a_1(N) = \begin{cases} 23/10, & N < 8,\\ 3, & N \ge 8. \end{cases}
--   $$
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Section 3, p.5

import Mathlib

namespace ReserveLB

/-- **First-risk budget `a_1(N)`.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Section 3, p.5: "a1(N) = 23/10 for N < 8, 3 for N ≥ 8".

`aOne N = 23/10` if `N < 8`, and `3` otherwise.

**Formalization Note.** A real number. -/
noncomputable def aOne (N : ℕ) : ℝ :=
  if N < 8 then 23 / 10 else 3

end ReserveLB


