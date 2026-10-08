-- Prove2me | Definitions.Def_BurnInBatch_ReleaseTmax_DP1
-- name    : BurnInBatch_ReleaseTmax_DP1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T13:28:32.958539+00:00
-- url     : https://prove2.me/theorems/fd57cbcd-5dfa-4c68-85a2-d82549944758
-- title:
--   Algorithm DP1: $f(j) = \min_{\max\{1, j-B+1\} \le i \le j} f_i(j)$
-- statement:
--   **Algorithm DP1** (§3, p. 768) for $1/r_i, p_i = p, B/T_{\max}$. Index the jobs $1, \dots, n$. Let $f(j)$ denote the minimum finishing time for jobs $1, \dots, j$ if they can be scheduled feasibly (every job on time), and infinity otherwise. Then $f(0) = 0$ and, for $j \ge 1$,
--   $$
--   f(j) = \min_{\max\{1,\, j-B+1\} \le i \le j} f_i(j),
--   \qquad
--   f_i(j) =
--   \begin{cases}
--   \max\{f(i-1), r_j\} + p, & \text{if } \max\{f(i-1), r_j\} + p \le d_i,\\
--   \infty, & \text{otherwise.}
--   \end{cases}
--   $$
--   Here $f_i(j)$ is the completion time of jobs $1$ through $j$ when jobs $i, i+1, \dots, j$ are processed in the last batch: that batch starts once the previous jobs are finished and job $j$ is released, and it is on time when it meets the due date $d_i$.
--
--   This is the dynamic program whose value the mission's goal theorem identifies with the minimum makespan of an on-time schedule.
--
--   **Formalization Note** `dp1 B p r d j` is $f(j)$ for prefix lengths $j \in \mathbb N$, computed in $\mathbb N_\infty$ (`ℕ∞`), with $\infty = \top$; the minimum is `Finset.inf` over $i \in [\max\{1, j-B+1\}, j]$ (natural-number subtraction, so the lower end is $1$ whenever $j - B + 1 \le 1$), and the paper's "$f(j) = \infty$ for $j < 0$" is vacuous for natural prefix lengths. Indices $i, j$ are 1-based as in the paper: $r_j$ is `jobVal r (j - 1)` and $d_i$ is `jobVal d (i - 1)`, where `jobVal f k` is the datum of the 0-based job $k$ for $k < n$ and $0$ for $k \ge n$ (those values are never used for $j \le n$). The running time $O(nB)$ is not formalized.
-- source:
--   Lee, Uzsoy & Martin-Vega, Efficient Algorithms for Scheduling Semiconductor Burn-In Operations, Oper. Res. 40(4) (1992), p. 768, §3, Algorithm DP1

import Mathlib
import Definitions.Def_BurnInBatch_ReleaseTmax_Model

namespace BurnInBatch.ReleaseTmax

/-- A job datum extended to all natural-number indices: the value of the 0-based job `k` for
`k < n`, and `0` beyond (those values are never used for prefix lengths `j ≤ n`). -/
def jobVal {n : ℕ} (f : Fin n → ℕ) (k : ℕ) : ℕ :=
  if h : k < n then f ⟨k, h⟩ else 0

/-- Algorithm DP1 (p. 768). `dp1 B p r d j` is the paper's `f(j)` for the prefix of length `j`:
`f(0) = 0` and, for `j ≥ 1`,
`f(j) = min_{max{1, j − B + 1} ≤ i ≤ j} f_i(j)` with
`f_i(j) = max{f(i − 1), r_j} + p` if `max{f(i − 1), r_j} + p ≤ d_i`, and `∞` otherwise.
Indices `i, j` are 1-based as in the paper: `r_j = jobVal r (j - 1)`, `d_i = jobVal d (i - 1)`.
The value `∞` is `⊤ : ℕ∞`, and a minimum over an empty range would be `⊤`. -/
noncomputable def dp1 {n : ℕ} (B p : ℕ) (r d : Fin n → ℕ) : ℕ → ℕ∞
  | 0 => 0
  | j + 1 =>
      (Finset.Icc (max 1 (j + 1 + 1 - B)) (j + 1)).attach.inf fun i =>
        have : i.val - 1 < j + 1 := by
          have := (Finset.mem_Icc.mp i.property).2
          omega
        let s : ℕ∞ := max (dp1 B p r d (i.val - 1)) (jobVal r j : ℕ∞) + p
        if s ≤ (jobVal d (i.val - 1) : ℕ∞) then s else ⊤
termination_by j => j

end BurnInBatch.ReleaseTmax


