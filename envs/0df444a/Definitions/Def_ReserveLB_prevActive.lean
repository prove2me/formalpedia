-- Prove2me | Definitions.Def_ReserveLB_prevActive
-- name    : ReserveLB_prevActive
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:29:08.897297+00:00
-- url     : https://prove2.me/theorems/b4f586a6-a81f-44b3-81e3-d3043189ede1
-- title:
--   Previous active class $g(q,h)$
-- statement:
--   For a multiplicity vector $q$ and a class $h$, $g(q, h)$ is the last active class before $h$, if there is one. For an active class $h$ there is none exactly when $h = f(q)$.
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Section 3, p.5

import Mathlib

namespace ReserveLB

/-- **Previous active class `g(q, h)`.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Section 3, p.5: "Write f(q), g(q, h), ℓ(q, h) for the first, previous and next active
classes."

`prevActive q h` is the largest active class below `h`, or `none` if `h` has no earlier active
class (for active `h`, exactly when `h = f(q)`).

**Formalization Note.** Classes are `Fin L`, ordered fastest first. -/
def prevActive {L : ℕ} (q : Fin L → Fin 3) (h : Fin L) : Option (Fin L) :=
  ((List.finRange L).filter fun g => g < h ∧ q g ≠ 0).getLast?

end ReserveLB


