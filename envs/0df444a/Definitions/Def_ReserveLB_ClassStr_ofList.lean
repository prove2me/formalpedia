-- Prove2me | Definitions.Def_ReserveLB_ClassStr_ofList
-- name    : ReserveLB_ClassStr_ofList
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:30:02.148068+00:00
-- url     : https://prove2.me/theorems/525f1a34-4f7a-435e-84cc-4905df0bba99
-- title:
--   Class structure written as a list
-- statement:
--   A list of pairs $(S_h, N_h)$ of rational speeds and natural counts defines the class structure with one class per entry, in order.
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Lemma 2.2, p.3

import Mathlib
import Definitions.Def_ReserveLB_ClassStr

namespace ReserveLB

/-- **Class structure written as a list.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Lemma 2.2, p.3: the constructed classes with "speeds Sh, counts Nh".

`ClassStr.ofList l` has one class per entry `(S_h, N_h)` of `l`, in order.

**Formalization Note.** Speeds are cast from `ℚ` to `ℝ`. -/
noncomputable def ClassStr.ofList (l : List (ℚ × ℕ)) : ClassStr :=
  ⟨l.length, fun h => (((l.get h).1 : ℚ) : ℝ), fun h => (l.get h).2⟩

end ReserveLB


