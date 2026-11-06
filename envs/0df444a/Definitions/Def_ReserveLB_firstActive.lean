-- Prove2me | Definitions.Def_ReserveLB_firstActive
-- name    : ReserveLB_firstActive
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:29:09.036027+00:00
-- url     : https://prove2.me/theorems/48e70d8d-a404-4d75-aac8-74f6bf3349ae
-- title:
--   First active class $f(q)$
-- statement:
--   For a multiplicity vector $q$, $f(q)$ is the first (fastest) class $h$ with $q_h \ne 0$, if there is one.
--
--   **Formalization Note** The value is optional; every pattern has an active class.
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Section 3, p.5

import Mathlib

namespace ReserveLB

/-- **First active class `f(q)`.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Section 3, p.5: "Write f(q), g(q, h), ℓ(q, h) for the first, previous and next active
classes."

`firstActive q` is the smallest class `h` with `q_h ≠ 0` (classes are ordered fastest first), or
`none` if there is none.

**Formalization Note.** Every pattern has an active class, so the value is `some` on patterns. -/
def firstActive {L : ℕ} (q : Fin L → Fin 3) : Option (Fin L) :=
  (List.finRange L).find? fun h => q h ≠ 0

end ReserveLB


