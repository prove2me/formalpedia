-- Prove2me | Definitions.Def_ReserveLB_ClassStr_vspeed
-- name    : ReserveLB_ClassStr_vspeed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:31:12.102764+00:00
-- url     : https://prove2.me/theorems/8de204bb-c521-46db-a337-c882601f7bd6
-- title:
--   Speed of a virtual machine
-- statement:
--   The virtual machine $(h, t)$ has speed $S_h$, the speed of its class.
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Lemma 2.2, p.3

import Mathlib
import Definitions.Def_ReserveLB_ClassStr
import Definitions.Def_ReserveLB_ClassStr_VM

namespace ReserveLB

/-- **Speed of a virtual machine.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Lemma 2.2, p.3: class `h` has speed `S_h`.

`C.vspeed (h, t) = S_h`.

**Formalization Note.** Used as the speed function of `Tsig` on the virtual machines. -/
def ClassStr.vspeed (C : ClassStr) (v : C.VM) : ℝ :=
  C.S v.1

end ReserveLB


