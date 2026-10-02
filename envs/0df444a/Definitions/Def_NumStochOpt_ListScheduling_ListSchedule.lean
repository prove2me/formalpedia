-- Prove2me | Definitions.Def_NumStochOpt_ListScheduling_ListSchedule
-- name    : NumStochOpt_ListScheduling_ListSchedule
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T20:55:25.372498+00:00
-- url     : https://prove2.me/theorems/7c7690e9-f67c-4df4-b8f8-9696059151e9
-- title:
--   The list-scheduling heuristic and its makespan $C^H_n(m)$
-- statement:
--   This file fixes the list-scheduling heuristic for the makespan problem on $m$ identical machines.
--
--   The jobs are placed in a fixed order, here $1, 2, \dots, n$, and at each step the next job on the list is assigned to the **first available machine**: the machine that becomes free earliest. Since machines are never left idle, machine $i$ becomes free at its current load $\ell_i$, so the first available machine is one of least current load; ties are broken towards the lowest machine index. Starting from $\ell \equiv 0$, after job $k$ is assigned to the first available machine $i^*$ its load becomes $\ell_{i^*} + p_k$. The **list-scheduling makespan** is the largest load after all $n$ jobs are assigned,
--
--   $$
--   C^H_n(m) = \max_{i=1,\dots,m} \ell^{(n)}_i .
--   $$
--
--   List scheduling is the heuristic whose makespan provides the upper bound in (8.10), and it is the second-stage heuristic $C^{H2}_n$ of the two-stage procedure of §8.3.
--
--   **Formalization Note** `lsLoads m p k` is the load vector after the first `k` jobs (0-based `p 0, …, p (k-1)`), defined by recursion on `k`. `firstAvailable ℓ` returns the least index among the machines of minimum load, and `none` only when `m = 0` (no machine; then no load changes). The book calls the order "arbitrary"; the index order is one such order, and the book's bounds hold for every order. The book leaves ties unspecified; the lowest-index rule is one admissible choice.
-- source:
--   A. H. G. Rinnooy Kan, L. Stougie, "Stochastic Integer Programming", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 8, p. 205, the list scheduling rule and C_n^H(m) (Figure 8.3, p. 206)

import Mathlib

namespace NumStochOpt.ListScheduling

/-- The first available machine given the current machine loads `ℓ`: a machine of least
current load, ties broken towards the lowest index (`none` only when `m = 0`). With
nonnegative processing times and no idle time, machine `i` becomes free at time `ℓ i`. -/
noncomputable def firstAvailable {m : ℕ} (ℓ : Fin m → ℝ) : Option (Fin m) :=
  if h : (Finset.univ.filter (fun i : Fin m => ∀ k, ℓ i ≤ ℓ k)).Nonempty then
    some ((Finset.univ.filter (fun i : Fin m => ∀ k, ℓ i ≤ ℓ k)).min' h)
  else none

/-- Machine loads after list scheduling the jobs `0, …, k-1` in index order on `m` machines:
each next job on the list is assigned to the first available machine. -/
noncomputable def lsLoads (m : ℕ) (p : ℕ → ℝ) : ℕ → Fin m → ℝ
  | 0 => fun _ => 0
  | k + 1 => fun i =>
      if firstAvailable (lsLoads m p k) = some i then lsLoads m p k i + p k
      else lsLoads m p k i

/-- The list-scheduling makespan `C^H_n(m)`: the maximum machine load after list scheduling
the first `n` jobs (in the fixed order `0, 1, …, n-1`) on `m` machines. -/
noncomputable def listMakespan (n m : ℕ) (p : ℕ → ℝ) : ℝ :=
  ⨆ i : Fin m, lsLoads m p n i

end NumStochOpt.ListScheduling


