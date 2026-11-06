-- Prove2me | Definitions.Def_ReserveLB_nextActive
-- name    : ReserveLB_nextActive
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:29:09.757582+00:00
-- url     : https://prove2.me/theorems/d4dc6454-7a8f-4a59-873a-191ebffd670f
-- title:
--   Next active class $\ell(q,h)$
-- statement:
--   For a multiplicity vector $q$ and a class $h$, $\ell(q, h)$ is the first active class after $h$, if there is one (none when $h$ is the last active class).
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Section 3, p.5

import Mathlib

namespace ReserveLB

/-- **Next active class `ℓ(q, h)`.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Section 3, p.5: "Write f(q), g(q, h), ℓ(q, h) for the first, previous and next active
classes."

`nextActive q h` is the smallest active class above `h`, or `none` when `h` is the last active
class.

**Formalization Note.** Classes are `Fin L`, ordered fastest first. -/
def nextActive {L : ℕ} (q : Fin L → Fin 3) (h : Fin L) : Option (Fin L) :=
  (List.finRange L).find? fun g => h < g ∧ q g ≠ 0

end ReserveLB


