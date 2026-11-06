-- Prove2me | Definitions.Def_ReserveLB_resOf
-- name    : ReserveLB_resOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:28:53.508983+00:00
-- url     : https://prove2.me/theorems/d074f11d-20a3-4425-9c10-36b27b2d0114
-- title:
--   Reservation sets written as lists of machine indices
-- statement:
--   A reservation is written as a list whose entry $j$ is a list of machine indices. The **reservation set** of job $j$ is the set of machines $i < m$ whose index occurs in entry $j$.
--
--   **Formalization Note** Indices are 0-based; repeated indices count once.
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Theorem 1.1, p.2 (reserved machines)

import Mathlib

namespace ReserveLB

/-- **The reservation sets written in a list of machine indices.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Theorem 1.1, p.2: the algorithm "reserves at most k distinct original machines per job".

`resOf m n res j` is the set of machines `i < m` whose index occurs in entry `j` of `res`.

**Formalization Note.** Machines and jobs are 0-based; repeated indices in an entry count once. -/
def resOf (m n : ℕ) (res : List (List ℕ)) : Fin n → Finset (Fin m) :=
  fun j => Finset.univ.filter fun i : Fin m => i.val ∈ res.getD j.val []

end ReserveLB


