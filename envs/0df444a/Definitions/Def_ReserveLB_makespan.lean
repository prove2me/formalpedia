-- Prove2me | Definitions.Def_ReserveLB_makespan
-- name    : ReserveLB_makespan
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:28:55.799448+00:00
-- url     : https://prove2.me/theorems/1eb8208d-1986-4dc5-a7e7-9c2b33d860d7
-- title:
--   Makespan $\max_i \sum_{j:\pi(j)=i} x_j/s_i$ of an assignment
-- statement:
--   Let machines $i \in M$ have speeds $s_i$, let $\pi$ assign every job $j$ to a machine and let $x_j$ be the job sizes. The **makespan** of $\pi$ is
--   $$
--   \max_{i \in M}\ \frac{1}{s_i}\sum_{j:\ \pi(j) = i} x_j .
--   $$
--
--   It is the cost minimized in $T_\sigma(x)$; the machine set is either the original machines or the virtual machines of Lemma 2.2.
--
--   **Formalization Note** The machine type is an arbitrary finite type; on an empty machine type the value is $0$, which is never used.
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Section 1, p.2 (definition of $T_\sigma$)

import Mathlib

namespace ReserveLB

/-- **Makespan of an assignment on machines with speeds.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Section 1, p.2: `max_i Σ_(j : π(j) = i) x_j / s_i` in the definition of `T_σ`.

For machines `M` with speeds `s`, an assignment `π` of jobs to machines and sizes `x`,
`makespan s π x = max_i (Σ_(j : π j = i) x_j) / s_i`.

**Formalization Note.** The machine type is arbitrary (original machines `Fin m`, or the virtual
machines of Lemma 2.2). On an empty machine type the value is `0`; it is never used there. -/
noncomputable def makespan {J M : Type*} [Fintype J] [Fintype M] [DecidableEq M]
    (s : M → ℝ) (π : J → M) (x : J → ℝ) : ℝ :=
  if h : (Finset.univ : Finset M).Nonempty then
    Finset.univ.sup' h fun i => (∑ j ∈ Finset.univ.filter (fun j => π j = i), x j) / s i
  else 0

end ReserveLB


