-- Prove2me | Definitions.Def_IgnallSchrage_MeanCompletion_Node
-- name    : IgnallSchrage_MeanCompletion_Node
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:28:36.070763+00:00
-- url     : https://prove2.me/theorems/3cdb57c5-6027-46f0-bf25-1465c80b06d3
-- title:
--   Nodes $J_r$, their unscheduled jobs $\bar J_r$, completion times $d_i$ and the sum of completion times (pp. 401, 405)
-- statement:
--   This file fixes the objects of the two-machine mean-completion-time problem of Ignall and Schrage.
--
--   There are $n$ jobs, numbered $0,1,\dots,n-1$ (the paper's jobs $1,\dots,n$, shifted by one). Job $i$ has real processing times $a_i$ on machine $A$ and $b_i$ on machine $B$, and every job visits $A$ first, then $B$.
--
--   1. A **full sequence** is a permutation $\sigma$ of the jobs, $\sigma(k)$ being the job in position $k$, processed in that order on both machines, each operation as early as possible from time $0$. The **completion time** $d_i(\sigma)$ of job $i$ is the time at which machine $B$ finishes it. The **sum of completion times** of $\sigma$ is
--   $$
--   \sum_{i=1}^{n} d_i(\sigma).
--   $$
--   2. A **node** $J_r$ of the search tree is a partial sequence: a list of $r$ jobs in the order in which they will be processed. Its **unscheduled set** $\bar J_r$ is the set of jobs not occurring in $J_r$.
--   3. For a node $J_r$, processing its jobs in order as early as possible gives each job $i\in J_r$ a completion time $d_i$; the node's attributes are $\sum_{i\in J_r} d_i$, the time $\sum_{j\in J_r} a_j$ at which machine $A$ finishes $J_r$, and $d_k$, the completion time of the last job $k$ of $J_r$. Appending job $i$ to a node at which machines $A$ and $B$ finish at $(T_A, T_B)$ gives
--   $$
--   T_A' = T_A + a_i,\qquad T_B' = \max(T_B, T_A') + b_i .
--   $$
--   4. A full sequence $\sigma$ **begins with** $J_r$ when $\sigma(k)$ is the $k$-th job of $J_r$ for every position $k<r$.
--
--   These are the objects of every statement of the mission. Completion times of full sequences are taken from Johnson's as-soon-as-possible schedule (the referenced definition `asapStart2`, which contains `asapC2`); node attributes follow the same recursion, so for a node $J_r$ with which $\sigma$ begins, the $d_i$ of $J_r$ agree with those of $\sigma$.
--
--   **Formalization Note** The paper minimizes the mean completion time $\frac1n\sum_i d_i$ and calls it equivalent to the sum (p. 405); since $n$ is fixed, the two have the same minimizers, and the mission uses the sum. A node is a `List (Fin n)`; every node the procedure creates, and every list a permutation begins with, is duplicate-free. For the root ($r=0$), which has no last job, $d_k$ is read as $0$. The restriction to permutation schedules is the paper's (p. 401, citing Johnson); no sign condition is imposed on the processing times.
-- source:
--   Ignall and Schrage, Application of the branch and bound technique to some flow-shop scheduling problems, Oper. Res. 13 (1965), p. 401, "Flowshop Problems as Trees" (nodes, permutation schedules), and p. 405, "M=2; A Lower Bound on Mean Completion Time for All Nodes Emanating from a Given Node" (a_i, b_i, d_i, J_r, J̄_r)

import Mathlib
import Definitions.Def_JohnsonFlowShop_TwoStage_asapStart2
import Definitions.Def_IgnallSchrage_Makespan_Node

namespace IgnallSchrage.MeanCompletion

/-- The pair (machine-A finish time, machine-B finish time) after one more job: from `(TA, TB)`
and job `i`, machine A finishes at `TA + a i` and machine B at `max TB (TA + a i) + b i`. This
is the IgnallSchrage.Makespan.step of `JohnsonFlowShop.TwoStage.asapC2`. -/
def appendJob {n : ℕ} (a b : Fin n → ℝ) (t : ℝ × ℝ) (i : Fin n) : ℝ × ℝ :=
  (t.1 + a i, max t.2 (t.1 + a i) + b i)

/-- `times a b J = (A(J), B(J))` for a node `J` (a partial sequence: the list of the jobs
scheduled so far, in order): the times at which machines A and B finish the last job of `J`
when the jobs of `J` are processed in the order of `J`, each operation as early as possible,
from time `0`. For `J = []` it is `(0, 0)`. For a nonempty `J` with last job `k`, the second
component is `d_k`, the completion time of `k` on machine B, and the first is
`Σ_{j ∈ J} a_j`. Whenever `J` is the list of the first `r` positions of an order `σ`, the
second component equals Johnson's `JohnsonFlowShop.TwoStage.asapC2 a b σ r`, since both apply
the same IgnallSchrage.Makespan.step position by position. -/
def times {n : ℕ} (a b : Fin n → ℝ) (J : List (Fin n)) : ℝ × ℝ :=
  J.foldl (appendJob a b) (0, 0)

/-- `lastCompletion a b J` is `d_k`, the completion time on machine B of the last job `k` of
the node `J` (the time machine B finishes the jobs of `J`). For the root `J = []`, which has
no last job, its value is `0`. -/
def lastCompletion {n : ℕ} (a b : Fin n → ℝ) (J : List (Fin n)) : ℝ :=
  (times a b J).2

/-- `nodeCompletionSum a b J = Σ_{i ∈ J} d_i`: the sum, over the jobs of the node `J`, of
their completion times on machine B when the jobs of `J` are processed in the order of `J` as
early as possible. The `m`-th job of `J` completes at `lastCompletion a b (J.take (m + 1))`. -/
def nodeCompletionSum {n : ℕ} (a b : Fin n → ℝ) (J : List (Fin n)) : ℝ :=
  ∑ m ∈ Finset.range J.length, lastCompletion a b (J.take (m + 1))

/-- The completion time `d_i` on machine B of job `i` in the as-soon-as-possible schedule of
the full sequence `σ` (`σ k` = job in position `k`): job `i` is in position `σ⁻¹ i`, and it
completes when machine B finishes the first `σ⁻¹ i + 1` positions (Johnson's `asapC2`). -/
def completionTime {n : ℕ} (a b : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (i : Fin n) : ℝ :=
  JohnsonFlowShop.TwoStage.asapC2 a b σ ((σ.symm i).val + 1)

/-- The sum of the completion times of a full sequence `σ`, `Σ_{i=1}^n d_i`. The paper's
objective is the mean completion time `(1/n) Σ_i d_i`; for a fixed `n` the two have the same
minimizers. -/
def totalCompletion {n : ℕ} (a b : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) : ℝ :=
  ∑ i : Fin n, completionTime a b σ i

end IgnallSchrage.MeanCompletion


