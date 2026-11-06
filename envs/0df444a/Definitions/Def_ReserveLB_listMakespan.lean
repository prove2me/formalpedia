-- Prove2me | Definitions.Def_ReserveLB_listMakespan
-- name    : ReserveLB_listMakespan
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:29:11.992423+00:00
-- url     : https://prove2.me/theorems/3d0fe866-a177-4414-bdff-0eeb545b4b43
-- title:
--   Makespan of a decoded assignment
-- statement:
--   For machines $0, \dots, m-1$ with speeds $s_i$, a decoded list $d$ (job $j$ goes to machine $d_j$) and sizes $x_j$, the makespan is
--   $$
--   \max_{i}\ \frac{1}{s_i}\sum_{j:\ d_j = i} x_j .
--   $$
--
--   It is the physical makespan $\mathrm{ms}_{\mathrm{decoder}}$ of Theorem 1.1.
--
--   **Formalization Note** A job whose entry is not a machine index counts on no machine; the theorems exclude this case by requiring a valid assignment.
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Theorem 1.1, p.2 ($\mathrm{ms}_{\mathrm{decoder}}$)

import Mathlib

namespace ReserveLB

/-- **Makespan of a decoded assignment.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Theorem 1.1, p.2: `ms_decoder(Σ, X)`, "one physical maximum" of the machine loads.

For speeds `s` of machines `Fin m`, a decoded list `d` (job `j` goes to machine `d_j`) and sizes `x`,
`listMakespan s d x = max_i (Σ_(j : d_j = i) x_j) / s_i`.

**Formalization Note.** A job whose entry is not a machine index contributes to no machine; the
theorems that use this exclude that case by `validAssign`. The value is `0` when `m = 0`. -/
noncomputable def listMakespan {m n : ℕ} (s : Fin m → ℝ) (d : List ℕ) (x : Fin n → ℝ) : ℝ :=
  if h : (Finset.univ : Finset (Fin m)).Nonempty then
    Finset.univ.sup' h fun i =>
      (∑ j ∈ Finset.univ.filter (fun j : Fin n => d.getD j.val 0 = i.val), x j) / s i
  else 0

end ReserveLB


