-- Prove2me | Definitions.Def_ReserveLB_portionY
-- name    : ReserveLB_portionY
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:29:59.301918+00:00
-- url     : https://prove2.me/theorems/d88e27fd-b21f-420a-8686-960271ad095f
-- title:
--   Exclusive size portion $Y_{jqh}$
-- statement:
--   For $T > 0$, a pattern $q$ and an active class $h$, the **exclusive portion** of a size $X_j$ is
--   $$
--   Y_{jqh} = X_j\,\mathbf 1\{T S_{\ell(q,h)} \le X_j < T S_h\},
--   $$
--   with lower cutoff $0$ when $h$ is the last active class. The portions of one size over the active classes are disjoint: $X_j$ falls into at most one of them, or into the exception $E_{jq}$.
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Section 3, p.5

import Mathlib
import Definitions.Def_ReserveLB_nextActive

namespace ReserveLB

/-- **Exclusive size portion `Y_jqh`.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Section 3, p.5: "For active h define the exclusive original-size portions
Yjqh = Xj 1{TSℓ(q,h) ≤ Xj < TSh} … with lower cutoff zero in the last class."

`portionY S T q h x = x` if `T · S_ℓ ≤ x < T · S_h`, where `ℓ = ℓ(q, h)` is the next active class
(lower cutoff `0` if `h` is the last active class), and `0` otherwise. Applied to the size `X_j`
it is `Y_jqh`.

**Formalization Note.** Only used for active `h`. -/
noncomputable def portionY {L : ℕ} (S : Fin L → ℝ) (T : ℝ) (q : Fin L → Fin 3) (h : Fin L)
    (x : ℝ) : ℝ :=
  if ((nextActive q h).map fun l => T * S l).getD 0 ≤ x ∧ x < T * S h then x else 0

end ReserveLB


