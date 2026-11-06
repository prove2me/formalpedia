-- Prove2me | Definitions.Def_ReserveLB_Pattern
-- name    : ReserveLB_Pattern
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:29:58.061081+00:00
-- url     : https://prove2.me/theorems/1e209159-bb4b-489a-8252-a49a843c3375
-- title:
--   Patterns $q$ with $q_h\in\{0,1,2\}$, $q_h\le N_h$, $1\le\sum_h q_h\le k$
-- statement:
--   A **pattern** assigns to every class $h$ a multiplicity $q_h \in \{0, 1, 2\}$ (absent, singleton or repeated) with
--   $$
--   q_h \le N_h \quad\text{for every } h,\qquad 1 \le \sum_h q_h \le k .
--   $$
--   A class $h$ is **active** in $q$ when $q_h \ne 0$.
--
--   Patterns are the columns of the system (4): a comparator's reservation is recorded by its capped multiplicities per class.
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Section 3, p.5

import Mathlib
import Definitions.Def_ReserveLB_ClassStr

namespace ReserveLB

/-- **Patterns.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Section 3, p.5: "A pattern q has qh ∈ {0, 1, 2}, qh ≤ Nh, and 1 ≤ Σ_h qh ≤ k: a class is
absent, singleton or repeated."

`Pattern C k` is the finite type of maps `q` from classes to `{0, 1, 2}` with `q_h ≤ N_h` for every
class and `1 ≤ Σ_h q_h ≤ k`.

**Formalization Note.** Values in `Fin 3`; a class `h` is active when `q_h ≠ 0`. -/
abbrev Pattern (C : ClassStr) (k : ℕ) : Type :=
  {q : Fin C.L → Fin 3 // (∀ h, (q h : ℕ) ≤ C.N h) ∧ 1 ≤ ∑ h, (q h : ℕ) ∧ ∑ h, (q h : ℕ) ≤ k}

end ReserveLB


