-- Prove2me | Definitions.Def_ReserveLB_lam
-- name    : ReserveLB_lam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:31:56.104325+00:00
-- url     : https://prove2.me/theorems/6830c213-f9f4-4c0c-9d09-c578cde6a159
-- title:
--   Prefix base $\lambda_{rh} = \lfloor P_h/A_r\rfloor$
-- statement:
--   For classes $r < h$, the **prefix base** is $\lambda_{rh} = \lfloor P_h / A_r \rfloor$; under (1) it is at least $1$.
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Section 3, p.5

import Mathlib
import Definitions.Def_ReserveLB_ClassStr
import Definitions.Def_ReserveLB_ClassStr_P
import Definitions.Def_ReserveLB_ClassStr_A

namespace ReserveLB

/-- **Prefix base `λ_rh`.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Section 3, p.5: "λrh = ⌊Ph/Ar⌋ ≥ 1".

`lam C r h = ⌊P_h / A_r⌋`.

**Formalization Note.** A natural floor; by (1) it is `≥ 1` for `r < h`. -/
noncomputable def lam (C : ClassStr) (r h : Fin C.L) : ℕ :=
  ⌊C.P h / C.A r⌋₊

end ReserveLB


