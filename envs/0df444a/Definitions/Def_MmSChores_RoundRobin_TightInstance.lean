-- Prove2me | Definitions.Def_MmSChores_RoundRobin_TightInstance
-- name    : MmSChores_RoundRobin_TightInstance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:25:37.071449+00:00
-- url     : https://prove2.me/theorems/5705a57c-1a97-4f88-aa06-f1e38bd1a94e
-- title:
--   Tight instance of Theorem 9 — (N − 1)·N chores worth −1/N and one chore worth −1 (p. 4)
-- statement:
--   The instance printed at the end of the proof of Theorem 9 (p. 4) to show that the factor $2-\tfrac1N$ cannot be improved.
--
--   Fix $N\ge 1$ agents. The item set is $\mathcal M=(t_1,t_2,\dots,t_{(N-1)N+1})$, with $(N-1)\cdot N+1$ chores, and every agent has the same utility function $d$:
--   $$d(t_j)=-\frac1N\quad (j=1,\dots,(N-1)N),\qquad d(t_{(N-1)N+1})=-1.$$
--
--   **Formalization Note** `tightUtil N : Fin ((N - 1) * N + 1) → ℝ`; chore index `j` (0-based) is worth `-(1 / N)` when `j < (N - 1) * N` and `-1` otherwise, so the $-1$ chore $t_{(N-1)N+1}$ is the last index `(N - 1) * N`. The profile in which every agent has this utility is `fun _ : Fin N => tightUtil N`. For `N ≥ 1` the subtraction `N - 1` is exact.
-- source:
--   Aziz, Rauchecker, Schryen & Walsh, Algorithms for Max-Min Share Fair Allocation of Indivisible Chores, AAAI 2017, PDF p. 4, proof of Theorem 9, last paragraph

import Mathlib

namespace MmSChores.RoundRobin

/-- The utility function of the tight instance in the proof of Theorem 9 (PDF p. 4): there are
`(N - 1) * N + 1` chores `t_1, …, t_{(N-1)N+1}`; the first `(N - 1) * N` of them (indices
`0, …, (N - 1) * N - 1`) are worth `-1/N` and the last one (index `(N - 1) * N`, the paper's
`t_{(N-1)N+1}`) is worth `-1`. Every agent has this same utility function. -/
noncomputable def tightUtil (N : ℕ) : Fin ((N - 1) * N + 1) → ℝ :=
  fun j => if (j : ℕ) < (N - 1) * N then -(1 / (N : ℝ)) else -1

end MmSChores.RoundRobin


