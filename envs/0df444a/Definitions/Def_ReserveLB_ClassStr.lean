-- Prove2me | Definitions.Def_ReserveLB_ClassStr
-- name    : ReserveLB_ClassStr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:29:07.657172+00:00
-- url     : https://prove2.me/theorems/81b0d790-a5b2-4b4a-89c2-23911b9f9ed7
-- title:
--   Virtual machine classes
-- statement:
--   A **class structure** has classes $h = 0, \dots, L-1$; class $C_h$ consists of $N_h$ virtual machines, each of speed $S_h$.
--
--   Lemma 2.2 constructs such classes from the original speeds; the necessity system (4) is written in terms of them.
--
--   **Formalization Note** Positivity of the speeds and the smoothness conditions (1) are separate hypotheses.
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Lemma 2.2, p.3

import Mathlib

namespace ReserveLB

/-- **Virtual machine classes.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Lemma 2.2, p.3: "virtual machines … with classes C0, …, CL−1, speeds Sh, counts Nh".

A class structure has `L` classes `h = 0, …, L − 1`; class `h` consists of `N_h` virtual machines,
each of speed `S_h`.

**Formalization Note.** Classes are `Fin L`; positivity of the speeds and the inequalities (1) are
separate hypotheses (`ClassStr.Smooth1`). -/
structure ClassStr where
  /-- the number of classes -/
  L : ℕ
  /-- the speed of the machines of each class -/
  S : Fin L → ℝ
  /-- the number of machines of each class -/
  N : Fin L → ℕ

end ReserveLB


