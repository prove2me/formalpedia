-- Prove2me | Definitions.Def_ReserveLB_ClassStr_A
-- name    : ReserveLB_ClassStr_A
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:30:59.937854+00:00
-- url     : https://prove2.me/theorems/1713e738-7631-4bfc-98e3-42ca63b377c8
-- title:
--   Prefix power $A_h = \sum_{f \le h} P_f$
-- statement:
--   The **prefix power** of class $h$ is
--   $$
--   A_h = \sum_{f \le h} P_f ,
--   $$
--   the total speed of the classes $0, \dots, h$ (fastest first).
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Lemma 2.2, p.3

import Mathlib
import Definitions.Def_ReserveLB_ClassStr
import Definitions.Def_ReserveLB_ClassStr_P

namespace ReserveLB

/-- **Prefix power.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Lemma 2.2, p.3: "prefixes Ah = Σ_(f≤h) Pf".

`C.A h = Σ_(f ≤ h) P_f`, the total speed of the classes `0, …, h`.

**Formalization Note.** `A_(−1) = 0` of (1) is written as the case `h = 0` in `Smooth1`. -/
noncomputable def ClassStr.A (C : ClassStr) (h : Fin C.L) : ℝ :=
  ∑ f ∈ Finset.univ.filter (fun f => f ≤ h), C.P f

end ReserveLB


