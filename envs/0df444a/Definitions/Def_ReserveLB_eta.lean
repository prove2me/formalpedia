-- Prove2me | Definitions.Def_ReserveLB_eta
-- name    : ReserveLB_eta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:29:26.539103+00:00
-- url     : https://prove2.me/theorems/80ec0311-1057-4901-8e28-f76fa4bdad72
-- title:
--   Enclosure width $\eta = 1/(16(n+1))$
-- statement:
--   The width of the lower enclosures is $\eta = 1/(16(n+1))$, where $n$ is the number of jobs.
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Section 3, p.5

import Mathlib

namespace ReserveLB

/-- **Enclosure width `η`.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Section 3, p.5: "Use rational lower enclosures of width η = 1/(16(n + 1))".

`eta n = 1 / (16 (n + 1))`, where `n` is the number of jobs.

**Formalization Note.** A real number. -/
noncomputable def eta (n : ℕ) : ℝ :=
  1 / (16 * ((n : ℝ) + 1))

end ReserveLB


