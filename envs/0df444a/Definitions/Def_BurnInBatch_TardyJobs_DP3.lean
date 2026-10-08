-- Prove2me | Definitions.Def_BurnInBatch_TardyJobs_DP3
-- name    : BurnInBatch_TardyJobs_DP3
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:37:18.146977+00:00
-- url     : https://prove2.me/theorems/006d28bb-dc5f-49db-9583-4a9f3cac27f9
-- title:
--   §4, Algorithm DP3: equal-length jobs and release times
-- statement:
--   For capacity $B$, common processing time $p$, releases $r_j$, and due dates $d_j$, the table $f(i,j)$ considers the first $j$ jobs and $i$ selected on-time jobs. Its values lie in $\mathbb N\cup\{+\infty\}$. The boundary conditions are $f(0,j)=0$ and $f(i,j)=+\infty$ for $i>j$. For $1\le i\le j\le n$,
--
--   $$
--   f(i,j)=\min\left\{f(i,j-1),\min_{1\le k\le\min(B,i)}f_k(i,j)\right\},
--   $$
--
--   where $f_k(i,j)=\max\{f(i-k,j-k),r_j\}+p$ if this value is at most $d_{j-k+1}$, and $f_k(i,j)=+\infty$ otherwise. The maximum number of on-time jobs represented by the table is $\max\{0\le i\le n:f(i,n)<+\infty\}$. This definition is the algorithmic side of the correctness target.
--
--   **Formalization Note** The paper's jobs are numbered from one; Lean uses zero-based `Fin n`, so its $r_j$ is evaluated at index $j-1$ and $d_{j-k+1}$ at index $j-k$. A minimum over an empty transition range is $+\infty$. The final range includes zero to handle all-tardy instances.
-- source:
--   Lee, Uzsoy & Martin-Vega, Efficient Algorithms for Scheduling Semiconductor Burn-In Operations, Oper. Res. 40(4) (1992), pp. 770–771, §4, Algorithm DP3 and displayed optimal-value formula

import Mathlib
import Definitions.Def_BurnInBatch_TardyJobs_Model

namespace BurnInBatch.TardyJobs

/-- Algorithm DP3, §4, pp. 770–771. `dp3 B p r d i j` is the minimum
completion time of exactly `i` on-time jobs among the first `j` jobs;
`⊤` means no such partial schedule exists. -/
def dp3 {n : ℕ} (B p : ℕ) (r d : Fin n → ℕ) (i j : ℕ) : WithTop ℕ :=
  if hi0 : i = 0 then 0
  else if hgt : i > j then ⊤
  else if hj : j ≤ n then
    have hi : i ≤ j := by omega
    have hjpos : 0 < j := by omega
    let skip := dp3 B p r d i (j - 1)
    let take := (Finset.Icc 1 (min B i)).attach.inf (fun k =>
      let start := max (dp3 B p r d (i - k.val) (j - k.val))
        ((r ⟨j - 1, by omega⟩ : ℕ) : WithTop ℕ)
      if start + ((p : ℕ) : WithTop ℕ) ≤
        ((d ⟨j - k.val, by have hk := Finset.mem_Icc.mp k.property; omega⟩ : ℕ) : WithTop ℕ)
      then start + ((p : ℕ) : WithTop ℕ) else ⊤)
    min take skip
  else ⊤
termination_by j
decreasing_by
  all_goals first | omega | (have hk := Finset.mem_Icc.mp k.property; omega)

/-- The largest feasible number of on-time jobs, including zero. -/
def dp3MaxOnTime {n : ℕ} (B p : ℕ) (r d : Fin n → ℕ) : ℕ :=
  Nat.findGreatest (fun i => dp3 B p r d i n ≠ ⊤) n

end BurnInBatch.TardyJobs


