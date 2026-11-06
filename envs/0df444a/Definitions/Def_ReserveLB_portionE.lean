-- Prove2me | Definitions.Def_ReserveLB_portionE
-- name    : ReserveLB_portionE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:30:00.696581+00:00
-- url     : https://prove2.me/theorems/ecbe8a33-6641-4337-a769-7439d0ee4ca5
-- title:
--   Full-exception portion $E_{jq}$
-- statement:
--   For $T > 0$ and a pattern $q$, the **full-exception portion** of $X_j$ is
--   $$
--   E_{jq} = X_j\,\mathbf 1\{X_j \ge T S_{f(q)}\}.
--   $$
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Section 3, p.5

import Mathlib
import Definitions.Def_ReserveLB_firstActive

namespace ReserveLB

/-- **Full-exception portion `E_jq`.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Section 3, p.5: "Ejq = Xj 1{Xj ≥ TSf(q)}".

`portionE S T q x = x` if `x ≥ T · S_(f(q))` and `0` otherwise. Applied to `X_j` it is `E_jq`.

**Formalization Note.** The value is `0` if `q` has no active class (never a pattern). -/
noncomputable def portionE {L : ℕ} (S : Fin L → ℝ) (T : ℝ) (q : Fin L → Fin 3) (x : ℝ) : ℝ :=
  match firstActive q with
  | some f => if T * S f ≤ x then x else 0
  | none => 0

end ReserveLB


