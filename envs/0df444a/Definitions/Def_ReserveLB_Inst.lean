-- Prove2me | Definitions.Def_ReserveLB_Inst
-- name    : ReserveLB_Inst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:29:07.236754+00:00
-- url     : https://prove2.me/theorems/0209ddb8-53e0-4a13-848f-c0ae314264b6
-- title:
--   Rational instance: speeds, listed laws and cap $k$
-- statement:
--   An **instance** consists of the machine speeds $s_1, \dots, s_m$ (rationals), for every job $j = 1, \dots, n$ its law as a list of rational atoms (value, probability), and the per-job reservation cap $k$.
--
--   The complete instance is the binary input of Theorem 1.1; its validity conditions are stated separately.
--
--   **Formalization Note** $m$ is the length of the speed list and $n$ the length of the law list; indices are 0-based.
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Section 1, p.2

import Mathlib

namespace ReserveLB

/-- **A rational input instance.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Section 1, p.2: "There are m positive rational machine speeds si, n independent
mandatory original sizes Xj ≥ 0, and input 1 ≤ k ≤ m. Finite marginal laws are explicitly listed
rationals; the complete input is binary encoded."

An instance lists the speeds `s_1, …, s_m`, for every job its law as a list of atoms
`(value, probability)`, and the reservation cap `k`.

**Formalization Note.** `m` is `speeds.length` and `n` is `laws.length`; machines and jobs are
0-based. Validity is the separate predicate `Inst.WellFormed`. -/
structure Inst where
  /-- the machine speeds -/
  speeds : List ℚ
  /-- the listed law of every job -/
  laws : List (List (ℚ × ℚ))
  /-- the per-job reservation cap -/
  k : ℕ

end ReserveLB


