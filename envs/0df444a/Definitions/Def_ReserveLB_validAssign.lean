-- Prove2me | Definitions.Def_ReserveLB_validAssign
-- name    : ReserveLB_validAssign
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:29:07.204864+00:00
-- url     : https://prove2.me/theorems/3a074721-2244-4be7-b50c-9a1ad7b1f92b
-- title:
--   Whole-job assignment inside the written reservations
-- statement:
--   A decoded list $d$ is a **valid whole-job assignment** for a written reservation if it has one entry per job and entry $j$ (the machine that receives job $j$) is one of the machines written for job $j$.
--
--   This is the requirement that the recourse sends every original, whole, to a machine of its written set.
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), proof of Theorem 1.1, p.13

import Mathlib

namespace ReserveLB

/-- **A whole-job assignment inside the written reservations.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), proof of Theorem 1.1, p.13: "each original is assigned once, whole, to its written set".

`validAssign n res d` says that the decoded list `d` has one entry per job, and entry `j` (the
machine of job `j`) occurs in the reservation `res` of job `j`.

**Formalization Note.** 0-based indices; entry `j` of a list is read with `getD`. -/
def validAssign (n : ℕ) (res : List (List ℕ)) (d : List ℕ) : Prop :=
  d.length = n ∧ ∀ j : Fin n, d.getD j.val 0 ∈ res.getD j.val []

end ReserveLB


