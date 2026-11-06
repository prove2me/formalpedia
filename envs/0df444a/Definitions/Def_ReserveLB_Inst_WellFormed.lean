-- Prove2me | Definitions.Def_ReserveLB_Inst_WellFormed
-- name    : ReserveLB_Inst_WellFormed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:30:17.235219+00:00
-- url     : https://prove2.me/theorems/1871303b-3d0b-4b57-bc8b-45e104ee79cc
-- title:
--   Well-formed instance
-- statement:
--   An instance is **well-formed** if
--   1. there is at least one machine and every speed is positive;
--   2. $1 \le k \le m$;
--   3. every job's list is a listed finite law of a nonnegative size (nonempty, values $\ge 0$, probabilities $> 0$, summing to one).
--
--   Nothing else is excluded: $n = 0$, $m = 1$, $k = m$, repeated atom values and arbitrary speed ratios are allowed.
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Section 1, p.2

import Mathlib
import Definitions.Def_ReserveLB_Inst
import Definitions.Def_ReserveLB_LawOK

namespace ReserveLB

/-- **Well-formed instance.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Section 1, p.2: "m positive rational machine speeds si, n independent mandatory original
sizes Xj ≥ 0, and input 1 ≤ k ≤ m"; "positive probabilities are unrestricted".

`I.WellFormed` says that there is at least one machine, every speed is positive, `1 ≤ k ≤ m`,
and every listed law is a finite probability law of a nonnegative size (`LawOK`).

**Formalization Note.** `n = 0`, `m = 1`, `k = m` and repeated atom values are all allowed. -/
def Inst.WellFormed (I : Inst) : Prop :=
  I.speeds ≠ [] ∧ (∀ s ∈ I.speeds, 0 < s) ∧ 1 ≤ I.k ∧ I.k ≤ I.speeds.length ∧
    ∀ μ ∈ I.laws, LawOK μ

end ReserveLB


