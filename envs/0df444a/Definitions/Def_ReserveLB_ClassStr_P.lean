-- Prove2me | Definitions.Def_ReserveLB_ClassStr_P
-- name    : ReserveLB_ClassStr_P
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:29:58.669305+00:00
-- url     : https://prove2.me/theorems/ed5b89dd-09cf-491a-97e1-56fb63fbdb8b
-- title:
--   Class power $P_h = N_h S_h$
-- statement:
--   The **power** of class $h$ is $P_h = N_h S_h$, the total speed of its machines.
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Lemma 2.2, p.3

import Mathlib
import Definitions.Def_ReserveLB_ClassStr

namespace ReserveLB

/-- **Power of a class.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Lemma 2.2, p.3: "powers Ph = NhSh".

`C.P h = N_h · S_h`, the total speed of class `h`.

**Formalization Note.** A real number. -/
noncomputable def ClassStr.P (C : ClassStr) (h : Fin C.L) : ℝ :=
  (C.N h : ℝ) * C.S h

end ReserveLB


