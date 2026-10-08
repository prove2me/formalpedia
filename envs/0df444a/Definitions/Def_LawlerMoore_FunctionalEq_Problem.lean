-- Prove2me | Definitions.Def_LawlerMoore_FunctionalEq_Problem
-- name    : LawlerMoore_FunctionalEq_Problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T12:42:22.949263+00:00
-- url     : https://prove2.me/theorems/43f5f50c-941f-4748-b9f0-ca52ba3781af
-- title:
--   Section 1 — two-mode jobs in a fixed order: feasible timings, total loss, and the minimum-loss value sets
-- statement:
--   Let $n$ jobs be performed one at a time in the fixed order $1, 2, \dots, n$. Job $j$ can be performed in either of two modes: in the first mode it requires $a_j$ units of time and incurs a loss $\alpha_j(t)$ when it is completed at time $t$; in the other mode it requires $b_j$ units of time and incurs the loss $\beta_j(t)$. Times are nonnegative integers.
--
--   1. **Modes and processing times.** A mode assignment $m$ chooses a mode for each job; the processing time of job $j$ is $p_j = a_j$ in the first mode and $p_j = b_j$ in the other.
--   2. **Feasible timings.** A timing of the first $j$ jobs is a vector of completion times $c_1, \dots, c_j \in \mathbb N$ with
--   $$c_{i-1} + p_i \le c_i \qquad (i = 1, \dots, j), \qquad c_0 := 0 .$$
--   Each job starts no earlier than time $0$ and no earlier than the completion of its predecessor; idle time between jobs is allowed.
--   3. **Total loss.** The total loss of the first $j$ jobs is
--   $$L_j(m, c) = \sum_{i=1}^{j} \begin{cases} \alpha_i(c_i) & \text{if job } i \text{ is in the first mode},\\ \beta_i(c_i) & \text{otherwise.}\end{cases}$$
--   4. **Value sets.** For $j \le n$ and an integer $t$, $\mathcal L(j, t)$ is the set of total losses $L_j(m, c)$ over all mode assignments $m$ and all feasible timings $c$ of the first $j$ jobs with $c_j \le t$ (for $j = 0$ the constraint reads $0 \le t$, and the only loss is the empty sum $0$).
--
--   The paper's "minimum total loss for the first $j$ jobs, subject to the constraint that job $j$ is completed no later than time $t$" is the least element of $\mathcal L(j, t)$. It is defined here directly from the scheduling problem, independently of the recursion (1).
--
--   **Formalization Note** Jobs are `Fin n`, 0-based: Lean job `i` is the paper's job $i+1$. Modes are `Bool` (`true` is the first mode, with $a$ and $\alpha$). `doneAt c k` is the completion time of the paper's job $k$ ($0$ for $k = 0$). Processing times are natural numbers and may be $0$; losses are arbitrary real functions of the natural-number completion time. Values of `m`, `c` on jobs after the first $j$ are ignored.
-- source:
--   Lawler, Moore, A Functional Equation and Its Application to Resource Allocation and Sequencing Problems, Management Sci. 16 (1969), p. 77, Section 1

import Mathlib

namespace LawlerMoore.FunctionalEq

/-! The two-mode, fixed-order problem of Lawler and Moore (1969), Section 1, p. 77.

There are `n` jobs, `Fin n`, performed one at a time in the fixed order `0, 1, …, n - 1`
(Lean job `i` is the paper's job `i + 1`). A mode assignment is `m : Fin n → Bool`:
`m i = true` is the first mode (processing time `a i`, loss `α i (completion time)`),
`m i = false` the other mode (processing time `b i`, loss `β i (completion time)`).
Time is a nonnegative integer. A timing is a vector of completion times `c : Fin n → ℕ`;
idle time between jobs is allowed. -/

/-- The processing time of job `i` under the mode assignment `m`: `a i` in the first mode,
`b i` in the other. -/
def procTime {n : ℕ} (a b : Fin n → ℕ) (m : Fin n → Bool) (i : Fin n) : ℕ :=
  if m i then a i else b i

/-- `doneAt c k` is the completion time of the paper's job `k`, i.e. of Lean job `k - 1`,
for `1 ≤ k ≤ n`, and `0` for `k = 0` (nothing is processed before time `0`). For `k > n`
the value is `0` and is never used. -/
def doneAt {n : ℕ} (c : Fin n → ℕ) (k : ℕ) : ℕ :=
  if h : 0 < k ∧ k ≤ n then c ⟨k - 1, by omega⟩ else 0

/-- `IsFeasible a b m c j`: the completion times `c` are a feasible timing of the first `j`
jobs under the mode assignment `m`. Each of these jobs starts no earlier than the completion
of the previous job (time `0` for the first job) and runs for its processing time, so
`c_{i-1} + p_i ≤ c_i`; idle time is allowed. The values of `m` and `c` on the jobs after the
first `j` are irrelevant. -/
def IsFeasible {n : ℕ} (a b : Fin n → ℕ) (m : Fin n → Bool) (c : Fin n → ℕ) (j : ℕ) : Prop :=
  ∀ i : Fin n, i.val < j → doneAt c i.val + procTime a b m i ≤ c i

/-- The total loss of the first `j` jobs under modes `m` and completion times `c`:
`∑_{i < j}` of `α i (c i)` if job `i` runs in the first mode, and `β i (c i)` otherwise. -/
def totalLoss {n : ℕ} (α β : Fin n → ℕ → ℝ) (m : Fin n → Bool) (c : Fin n → ℕ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < j), if m i then α i (c i) else β i (c i)

/-- The set of total losses of the first `j` jobs over all mode assignments and all feasible
timings in which the paper's job `j` is completed no later than time `t` (for `j = 0` the
constraint reads `0 ≤ t`). Its least element, when it exists, is the paper's
"minimum total loss for the first `j` jobs, subject to the constraint that job `j` is
completed no later than time `t`". -/
def lossesBy {n : ℕ} (a b : Fin n → ℕ) (α β : Fin n → ℕ → ℝ) (j : ℕ) (t : ℤ) : Set ℝ :=
  {L | ∃ (m : Fin n → Bool) (c : Fin n → ℕ),
    IsFeasible a b m c j ∧ ((doneAt c j : ℕ) : ℤ) ≤ t ∧ L = totalLoss α β m c j}

end LawlerMoore.FunctionalEq


