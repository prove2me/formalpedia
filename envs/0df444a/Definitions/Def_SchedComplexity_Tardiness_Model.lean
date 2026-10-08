-- Prove2me | Definitions.Def_SchedComplexity_Tardiness_Model
-- name    : SchedComplexity_Tardiness_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:42:08.017224+00:00
-- url     : https://prove2.me/theorems/9dcbd783-5087-48ba-adb4-fecad4cdf12a
-- title:
--   The single-machine problem $n|1||\sum w_jT_j$: schedules, tardiness, processing orders
-- statement:
--   The model of Section 3 of the paper, specialised to one machine, all release dates $0$, and the criterion $\sum w_jT_j$.
--
--   A finite set of jobs is given; job $j$ has a processing time $p_j$, a weight $w_j$ and a due date $d_j$, all nonnegative integers. A **schedule** assigns every job a start time $B_j\in\mathbb N$; it is **feasible** if no two distinct jobs overlap on the machine, i.e. for $i\ne j$ either $B_i+p_i\le B_j$ or $B_j+p_j\le B_i$. The **completion time** is $C_j=B_j+p_j$, the **tardiness** is $T_j=\max\{0,C_j-d_j\}$, and the instance with threshold $y$ is a yes-instance when some feasible schedule satisfies
--
--   $$\sum_j w_jT_j\le y.$$
--
--   For jobs numbered $1,\dots,n$, a **processing order** is a permutation $\pi=(\pi(1),\dots,\pi(n))$. Its schedule **without idle time** processes the jobs in that order from time $0$ without interruption; the job in position $k$ completes at
--
--   $$C_{\pi(k)}=\sum_{i\le k}p_{\pi(i)}.$$
--
--   Finally, for a function $v$ on the jobs and a position $t$, the quantity $\sum_{j>t}v_{\pi(j)}\big(C_{\pi(j)}-C_{\pi(t)}\big)$ (used with $v=w$, $v=p$ and $v\equiv1$ in the proof of Theorem 4(d)) is defined.
--
--   **Formalization Note** Start times are natural numbers, as in the paper, where schedules are determined by processing orders and all data are integers ("Given a processing order on each machine, we can compute for each job ... the starting time $B_j$", p. 6); every criterion is regular, so this loses nothing. Tardiness and the objective are computed in $\mathbb Z$. A job of zero length may sit at the boundary of another job's interval. In the order-based part jobs are `Fin n` and positions are 0-based: `π i` is the paper's $\pi(i+1)$, and `posCompletion p π k` is $C_{\pi(k)}$ for the 1-based position $k$ ($0$ for $k=0$). `tailWeighted p v π t` sums over the 0-based positions $i\ge t$, i.e. the 1-based positions $j>t$.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), pp. 6–7, Section 3; p. 20, proof of Theorem 4(d)

import Mathlib

namespace SchedComplexity.Tardiness

/-! # The single-machine total weighted tardiness problem `n|1||Σw_jT_j`

Brucker, Lenstra & Rinnooy Kan 1975, Section 3 (pp. 6–7). Jobs form a finite type `J`; job `j`
has processing time `p j`, weight `w j` and due date `d j`, all in `ℕ` (zero allowed); all release
dates are `0`. A schedule assigns every job a start time in `ℕ`. -/

/-- A schedule `S` (start times) on one machine is feasible iff no two distinct jobs overlap:
job `j` occupies `[S j, S j + p j)`, so for `i ≠ j` one of them finishes before the other starts.
Start times are natural numbers, hence `≥ 0 = r_j`. -/
def IsFeasible {J : Type*} (p : J → ℕ) (S : J → ℕ) : Prop :=
  ∀ i j : J, i ≠ j → S i + p i ≤ S j ∨ S j + p j ≤ S i

/-- Completion time `C_j = B_j + p_j` of job `j` under the start times `S`. -/
def completion {J : Type*} (p : J → ℕ) (S : J → ℕ) (j : J) : ℕ :=
  S j + p j

/-- Tardiness `T_j = max{0, C_j − d_j}`, computed in `ℤ`. -/
def tardiness {J : Type*} (p d : J → ℕ) (S : J → ℕ) (j : J) : ℤ :=
  max 0 ((completion p S j : ℤ) - d j)

/-- Total weighted tardiness `Σ_j w_j T_j` of the schedule `S`. -/
def totalWeightedTardiness {J : Type*} [Fintype J] (p w d : J → ℕ) (S : J → ℕ) : ℤ :=
  ∑ j, (w j : ℤ) * tardiness p d S j

/-- The instance `(p, w, d)` of `n|1||Σw_jT_j` with threshold `y` is a yes-instance: some feasible
schedule has `Σ_j w_j T_j ≤ y`. -/
def HasScheduleLE {J : Type*} [Fintype J] (p w d : J → ℕ) (y : ℕ) : Prop :=
  ∃ S : J → ℕ, IsFeasible p S ∧ totalWeightedTardiness p w d S ≤ (y : ℤ)

/-! ## Processing orders and their schedules without idle time

Jobs `Fin n`; a processing order is a permutation `π` with `π i` the job in the (0-based) position
`i`, i.e. the paper's `π(i+1)`. -/

/-- `C_π(k)` for the paper's 1-based position `k`: the completion time of the `k`-th job when the
jobs are processed in the order `π` without interruption from time `0`, namely the total
processing time of the first `k` positions, `Σ_{i < k} p_{π(i)}` (0-based `i`). It is `0` for
`k = 0` and `Σ_j p_j` for `k ≥ n`. -/
def posCompletion {n : ℕ} (p : Fin n → ℕ) (π : Equiv.Perm (Fin n)) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), p (π i)

/-- The start times of the schedule without idle time of the order `π`: job `j`, in the 0-based
position `π⁻¹ j`, starts when the jobs in the earlier positions are finished. Its completion time
is `posCompletion p π ((π⁻¹ j) + 1)`. -/
def noIdleStart {n : ℕ} (p : Fin n → ℕ) (π : Equiv.Perm (Fin n)) : Fin n → ℕ :=
  fun j => posCompletion p π (π.symm j).val

/-- `Σ_j w_j T_j` of the schedule without idle time of the order `π`. -/
def orderTWT {n : ℕ} (p w d : Fin n → ℕ) (π : Equiv.Perm (Fin n)) : ℤ :=
  totalWeightedTardiness p w d (noIdleStart p π)

/-- `Σ_{j > t} v_{π(j)} (C_π(j) − C_π(t))` (1-based positions `j`, as in (1), (2), (4)–(7) of the
proof of Theorem 4(d), p. 20–21): the sum over the 0-based positions `i ≥ t` of
`v (π i) * (posCompletion p π (i+1) − posCompletion p π t)`, in `ℤ`. With `v = w` it is the
left side of (1), with `v = p` the first term of (1), and with `v ≡ 1` the second. -/
def tailWeighted {n : ℕ} (p v : Fin n → ℕ) (π : Equiv.Perm (Fin n)) (t : ℕ) : ℤ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => t ≤ i.val),
    (v (π i) : ℤ) * ((posCompletion p π (i.val + 1) : ℤ) - posCompletion p π t)

end SchedComplexity.Tardiness


