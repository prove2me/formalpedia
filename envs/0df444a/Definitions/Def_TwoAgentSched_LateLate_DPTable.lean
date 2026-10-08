-- Prove2me | Definitions.Def_TwoAgentSched_LateLate_DPTable
-- name    : TwoAgentSched_LateLate_DPTable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:38:43.878549+00:00
-- url     : https://prove2.me/theorems/790ea034-c154-4e29-8353-6d3e0eaa26b8
-- title:
--   §7: the dynamic-programming table $C(i,h,k)$ and partial schedules of $\{J_1,\dots,J_i\}$
-- statement:
--   The jobs $J_1, \dots, J_n$ of both agents are numbered in earliest-due-date (EDD) order. For $0 \le i \le n$ and $h, k \ge 0$, the table $C(i,h,k) \in \mathbb N \cup \{+\infty\}$ is computed by the boundary conditions and recursion relation of §7:
--   $$C(0,h,k) = 0, \qquad C(i,h,k) = +\infty \ \text{ if } h < 0 \text{ or } k < 0,$$
--   $$f(i,h,k) = \begin{cases} +\infty & \text{if } C(i-1,h,k) + p_i > d_i,\\ 0 & \text{otherwise,}\end{cases}$$
--   $$C(i,h,k) = \begin{cases} \min\{C(i-1,h,k) + p_i + f(i,h,k);\ C(i-1,h-1,k)\} & \text{if } J_i \text{ belongs to } A,\\ \min\{C(i-1,h,k) + p_i + f(i,h,k);\ C(i-1,h,k-1)\} & \text{if } J_i \text{ belongs to } B,\end{cases}$$
--   with $+\infty + x = +\infty$.
--
--   A **partial schedule** of the job set $\{J_1, \dots, J_i\}$ with at most $h$ late $A$-jobs and at most $k$ late $B$-jobs is described by its set $E \subseteq \{J_1,\dots,J_i\}$ of early jobs: the jobs of $E$ are processed first, in EDD (index) order, each one completing by its due date,
--   $$\sum_{l \in E,\ l \le j} p_l \le d_j \quad \text{for every } J_j \in E,$$
--   and the remaining jobs of $\{J_1,\dots,J_i\}$ are late, at most $h$ of them belonging to $A$ and at most $k$ to $B$. The completion time of the last early job of such a partial schedule is $\sum_{j \in E} p_j$ (and $0$ when $E = \emptyset$).
--
--   The table is the dynamic program whose correctness is Lemma 7.2 and Theorem 7.3; the partial schedules are the objects its entries minimize over.
--
--   **Formalization Note** Values lie in `WithTop ℕ`, with `⊤` for $+\infty$. The paper prints only $C(0,0,0) = 0$ as boundary; $C(0,h,k) = 0$ for every $h,k \ge 0$ is the value forced by the definition ("at most" $h$ and $k$ late jobs of the empty set), and reading $C(0,h,k) = +\infty$ for $h + k > 0$ would make Theorem 7.3 false. A negative index $h - 1$ or $k - 1$ (at $h = 0$ or $k = 0$) gives $+\infty$. Rows $i > n$ do not occur in the paper; the definition repeats row $n$ there. Early means $C_j \le d_j$, as in the recursion (the proof of Lemma 7.2 prints a strict "$<$", a typo).
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 236, §7 (definition of C(i, h, k), Boundary Conditions, Recursion Relation; Lemma 7.1 structure of partial schedules)

import Mathlib
import Definitions.Def_TwoAgentSched_LateLate_Model

namespace TwoAgentSched.LateLate

/-- The table `C(i, h, k)` of the dynamic program of §7 (p. 236), computed by its boundary
conditions and recursion relation, with values in `WithTop ℕ` (`⊤` is `+∞`). Jobs are indexed
by `Fin n` in EDD order, 0-based (`⟨i, _⟩` is the job `J_{i+1}`), with processing times `p`,
due dates `d` and owners `ag`.

* Boundary: `C(0, h, k) = 0` for all `h, k ≥ 0`. The paper prints only `C(0, 0, 0) = 0`; for
  `h + k > 0` the value `0` is the one forced by the definition ("at most `h` late `A`-jobs and at
  most `k` late `B`-jobs" of the empty job set). A negative index gives `+∞`: here
  `C(i − 1, h − 1, k)` at `h = 0` and `C(i − 1, h, k − 1)` at `k = 0` are read as `⊤`.
* Recursion, for the job `J_i` (`i ≥ 1`):
  `f(i, h, k) = +∞` if `C(i − 1, h, k) + p_i > d_i`, and `0` otherwise;
  `C(i, h, k) = min{C(i − 1, h, k) + p_i + f(i, h, k); C(i − 1, h − 1, k)}` if `J_i` is an
  `A`-job, and `min{C(i − 1, h, k) + p_i + f(i, h, k); C(i − 1, h, k − 1)}` if it is a `B`-job.
* Rows `i > n` (no job `J_i`) repeat row `i − 1`; the paper uses only `i ≤ n`. -/
def C {n : ℕ} (p d : Fin n → ℕ) (ag : Fin n → Agent) : ℕ → ℕ → ℕ → WithTop ℕ
  | 0, _, _ => 0
  | i + 1, h, k =>
    if hi : i < n then
      let f : WithTop ℕ :=
        if C p d ag i h k + ((p ⟨i, hi⟩ : ℕ) : WithTop ℕ) ≤ ((d ⟨i, hi⟩ : ℕ) : WithTop ℕ) then 0
        else ⊤
      let lateBranch : WithTop ℕ :=
        match ag ⟨i, hi⟩ with
        | .A => if h = 0 then ⊤ else C p d ag i (h - 1) k
        | .B => if k = 0 then ⊤ else C p d ag i h (k - 1)
      min (C p d ag i h k + ((p ⟨i, hi⟩ : ℕ) : WithTop ℕ) + f) lateBranch
    else C p d ag i h k

/-- A set `E` of jobs can be processed first, in index (EDD) order, with every job of `E` early:
for each `j ∈ E`, the total processing time of the jobs of `E` up to and including `j` is at most
`d_j`. This is the early part of a partial schedule in the structure of Lemma 7.1 (§7, p. 236). -/
def IsEarlyFeasible {n : ℕ} (p d : Fin n → ℕ) (E : Finset (Fin n)) : Prop :=
  ∀ j ∈ E, ∑ i ∈ E.filter (fun i => i ≤ j), p i ≤ d j

/-- A partial schedule of the job set `{J_1, …, J_i}` with at most `h` late `A`-jobs and at most
`k` late `B`-jobs (§7, p. 236), described by its set `E ⊆ {J_1, …, J_i}` of early jobs: `E` is
processed first in EDD order with every job early (`IsEarlyFeasible`), and the other jobs of
`{J_1, …, J_i}` are late; at most `h` of them belong to `A` and at most `k` to `B`. The completion
time of the last early job of this partial schedule is `∑_{j ∈ E} p_j` (`0` if `E = ∅`). -/
def IsPartialSchedule {n : ℕ} (p d : Fin n → ℕ) (ag : Fin n → Agent) (i h k : ℕ)
    (E : Finset (Fin n)) : Prop :=
  E ⊆ prefixJobs n i ∧ IsEarlyFeasible p d E ∧
    ((prefixJobs n i \ E).filter (fun j => ag j = .A)).card ≤ h ∧
    ((prefixJobs n i \ E).filter (fun j => ag j = .B)).card ≤ k

end TwoAgentSched.LateLate


