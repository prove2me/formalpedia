-- Prove2me | Definitions.Def_GTWSched_MaxDisc_Model
-- name    : GTWSched_MaxDisc_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T07:31:58.7673+00:00
-- url     : https://prove2.me/theorems/5c247fdd-9854-4417-9b2c-9373a1fe9a15
-- title:
--   §3, pp. 342–344 — release times, deadlines of special form, feasible and optimum schedules, release time property, standard form
-- statement:
--   This file fixes the scheduling problem of §3 of Garey, Tarjan and Wilfong (1988). There are $N$ tasks on one processor; task $T_i$ has a length $l_i \ge 0$, a release time $r_i \ge 0$ and a deadline $d_i$ (real numbers). The tasks are indexed $0, \dots, N-1$ (the paper's $T_1, \dots, T_N$).
--
--   1. **Special form.** For a constant $\alpha$, the data are in special form if for every task either $d_i - r_i = l_i + \alpha$, or $r_i = 0$ and $d_i < l_i + \alpha$. (In the paper $\alpha = 2\gamma$ for the bound $\gamma$ on the maximum discrepancy.)
--   2. **Schedules.** A schedule is an execution order $\sigma$ (a permutation; $\sigma(p)$ is the task executed in position $p$) together with starting times $s_i$, such that whenever position $p$ precedes position $q$, $$s_{\sigma(p)} + l_{\sigma(p)} \le s_{\sigma(q)},$$ so execution intervals meet at most at their endpoints.
--   3. **Feasible:** every task starts no earlier than its release time and finishes no later than its deadline, $r_i \le s_i$ and $s_i + l_i \le d_i$.
--   4. **Makespan:** $\max_i (s_i + l_i)$, the completion time of the latest finishing task. **Optimum:** feasible, with makespan no larger than that of any feasible schedule.
--   5. **Release time property** with respect to a task $T_n$: every task executed after $T_n$ has a release time strictly later than the starting time $s_n$.
--   6. **Standard form with split index $j$** (for tasks indexed in nondecreasing order of deadlines, with the paper's $T_N$ the last task $N-1$): $0 \le j \le N-1$; the first $j$ positions hold exactly the tasks of index $< j$, and these form an optimum schedule of the sub-instance consisting of those tasks; position $j$ holds the last task, which starts at $\max(r_{N-1}, C)$ with $C$ the completion time of the first part ($C = 0$ when $j = 0$); positions $j+1, \dots, N-1$ hold the tasks of index $j, \dots, N-2$ in this order, each starting when the preceding one finishes.
--
--   These objects are the model of the decision version of minimizing the maximum discrepancy: Theorem 4, Corollaries 1 and 2 and the paper's linear-time algorithm are statements about them.
--
--   **Formalization Note.** Indices are 0-based, so the paper's split index $j$ (the number of real tasks before $T_N$) is unchanged but the paper's tasks $T_1, \dots, T_j$ are indices $0, \dots, j-1$. The paper's dummy task $T_0$ with $r_0 = d_0 = l_0 = 0$ is not a task here; its only role, that an empty first part completes at time $0$, is the value $0$ of the supremum over an empty index set in `firstPartCompletion` (and of `makespan` when $N = 0$). A schedule carries its execution order explicitly, so that "the tasks executed after $T_n$" is determined also when zero-length tasks share a starting time. The clause "(which can be assumed optimum)" of p. 344 is part of `StandardForm`. Start times are nonnegative because release times are.
-- source:
--   Garey, Tarjan & Wilfong, One-Processor Scheduling with Symmetric Earliness and Tardiness Penalties, Math. Oper. Res. 13 (1988), pp. 342–344, §3 (special form, feasible, optimum) and §3.1 (release time property p. 343; standard form and split index p. 344)

import Mathlib

namespace GTWSched.MaxDisc

/-- The special form of the release times and deadlines (p. 342): for every task `i`,
either `d i - r i = l i + α`, or `r i = 0` and `d i < l i + α` (strict). -/
def SpecialForm {N : ℕ} (r d l : Fin N → ℝ) (α : ℝ) : Prop :=
  ∀ i, d i - r i = l i + α ∨ (r i = 0 ∧ d i < l i + α)

/-- A one-processor schedule is an execution order `σ` (`σ p` is the task executed in
position `p`) together with starting times `s`. `Ordered l σ s` says that a task finishes
no later than any task executed after it starts, so execution intervals meet at most at
their endpoints. -/
def Ordered {N : ℕ} (l : Fin N → ℝ) (σ : Fin N ≃ Fin N) (s : Fin N → ℝ) : Prop :=
  ∀ p q : Fin N, p < q → s (σ p) + l (σ p) ≤ s (σ q)

/-- Feasible (p. 342): every task begins no sooner than its release time and finishes no
later than its deadline. -/
def Feasible {N : ℕ} (r d l : Fin N → ℝ) (σ : Fin N ≃ Fin N) (s : Fin N → ℝ) : Prop :=
  Ordered l σ s ∧ ∀ i, r i ≤ s i ∧ s i + l i ≤ d i

/-- The makespan: the completion time of the latest finishing task. For `N = 0` the
supremum over the empty type is `0`. -/
noncomputable def makespan {N : ℕ} (l s : Fin N → ℝ) : ℝ :=
  ⨆ i : Fin N, s i + l i

/-- Optimum (p. 342): feasible and of minimum makespan among all feasible schedules. -/
def Optimum {N : ℕ} (r d l : Fin N → ℝ) (σ : Fin N ≃ Fin N) (s : Fin N → ℝ) : Prop :=
  Feasible r d l σ s ∧
    ∀ (σ' : Fin N ≃ Fin N) (s' : Fin N → ℝ), Feasible r d l σ' s' → makespan l s ≤ makespan l s'

/-- The release time property (p. 343) with respect to task `n`: every task executed after
`n` has a release time strictly later than the time at which `n` starts. -/
def ReleaseTimeProperty {N : ℕ} (r : Fin N → ℝ) (σ : Fin N ≃ Fin N) (s : Fin N → ℝ)
    (n : Fin N) : Prop :=
  ∀ i, σ.symm n < σ.symm i → s n < r i

/-- The completion time of the first part of a schedule, made of the tasks of index `< j`
(the paper's `T₁, …, Tⱼ`); it is `0` when `j = 0`, the finishing time of the paper's dummy
task `T₀`. -/
noncomputable def firstPartCompletion {N : ℕ} (l s : Fin N → ℝ) (j : ℕ) : ℝ :=
  ⨆ i : {i : Fin N // i.val < j}, s i.1 + l i.1

/-- Standard form with split index `j` (p. 344), for tasks indexed in nondecreasing deadline
order with the paper's `T_N` the last index `N - 1`:
the positions `< j` hold exactly the tasks of index `< j`, and these form an optimum
schedule of the sub-instance of those tasks; position `j` holds the last task, which starts at
the maximum of its release time and the completion time of the first part; positions
`j + 1, …, N - 1` hold the tasks of index `j, …, N - 2` in this order, each starting when the
preceding one finishes. -/
structure StandardForm {N : ℕ} (r d l : Fin N → ℝ) (σ : Fin N ≃ Fin N) (s : Fin N → ℝ)
    (j : ℕ) : Prop where
  split_lt : j < N
  first_part : ∀ p : Fin N, p.val < j → (σ p).val < j
  first_part_optimum :
    (∀ p q : Fin N, p < q → q.val < j → s (σ p) + l (σ p) ≤ s (σ q)) ∧
    (∀ i : Fin N, i.val < j → r i ≤ s i ∧ s i + l i ≤ d i) ∧
    ∀ (σ' : Fin j ≃ Fin j) (s' : Fin j → ℝ),
      Feasible (fun i => r (Fin.castLE split_lt.le i)) (fun i => d (Fin.castLE split_lt.le i))
        (fun i => l (Fin.castLE split_lt.le i)) σ' s' →
      firstPartCompletion l s j ≤ makespan (fun i => l (Fin.castLE split_lt.le i)) s'
  split_task : ∀ p : Fin N, p.val = j → (σ p).val + 1 = N
  split_start : ∀ p : Fin N, p.val = j → s (σ p) = max (r (σ p)) (firstPartCompletion l s j)
  after_order : ∀ p : Fin N, j < p.val → (σ p).val + 1 = p.val
  after_no_idle : ∀ p q : Fin N, j ≤ p.val → q.val = p.val + 1 → s (σ q) = s (σ p) + l (σ p)

end GTWSched.MaxDisc


