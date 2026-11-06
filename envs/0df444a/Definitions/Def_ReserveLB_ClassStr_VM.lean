-- Prove2me | Definitions.Def_ReserveLB_ClassStr_VM
-- name    : ReserveLB_ClassStr_VM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:29:59.414241+00:00
-- url     : https://prove2.me/theorems/953101b4-b0bc-47a5-b395-e2ef41614277
-- title:
--   Virtual machines of a class structure
-- statement:
--   The **virtual machines** of a class structure are the pairs $(h, t)$ with $t < N_h$: machine $t$ of class $C_h$. There are $m' = \sum_h N_h$ of them.
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Lemma 2.2, p.3; p.4 ($m'$)

import Mathlib
import Definitions.Def_ReserveLB_ClassStr

namespace ReserveLB

/-- **The virtual machines of a class structure.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Lemma 2.2, p.3: the virtual machines of the classes `C_0, …, C_(L−1)`; p.4: "Write
m′ = Σ_h Nh for the virtual machine count".

A virtual machine is a pair `(h, t)` of a class `h` and a position `t < N_h`.

**Formalization Note.** A dependent pair type; it is finite, with `Σ_h N_h` elements. -/
abbrev ClassStr.VM (C : ClassStr) : Type :=
  (h : Fin C.L) × Fin (C.N h)

end ReserveLB


