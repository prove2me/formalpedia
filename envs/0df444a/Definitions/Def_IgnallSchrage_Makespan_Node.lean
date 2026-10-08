-- Prove2me | Definitions.Def_IgnallSchrage_Makespan_Node
-- name    : IgnallSchrage_Makespan_Node
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T11:56:32.901243+00:00
-- url     : https://prove2.me/theorems/7cf8d4a8-e0e7-40f3-a0a1-693dc07c3440
-- title:
--   Nodes $J_r$, their unscheduled jobs $\bar J_r$, TIMEA/TIMEB/TIMEC and the makespan (pp. 400–401)
-- statement:
--   This file fixes the objects of the three-machine makespan problem of Ignall and Schrage.
--
--   There are $n$ jobs, numbered $0,1,\dots,n-1$ (the paper's jobs $1,\dots,n$, shifted by one). Job $i$ has real processing times $a_i$, $b_i$, $c_i$ on machines $A$, $B$, $C$, and every job visits $A$, then $B$, then $C$.
--
--   1. A **node** $J_r$ of the search tree is a partial sequence: a list of $r$ jobs, in the order in which they will be processed. The **unscheduled set** $\bar J_r$ is the set of jobs not occurring in $J_r$.
--   2. For a node $J_r$, the attributes $\mathrm{TIMEA}(J_r)$, $\mathrm{TIMEB}(J_r)$, $\mathrm{TIMEC}(J_r)$ are the times at which machines $A$, $B$, $C$ finish the last of the $r$ jobs when the jobs of $J_r$ are processed in order, each operation as early as possible, from time $0$. Starting from $(0,0,0)$, appending job $i$ to a node with attributes $(T_A,T_B,T_C)$ gives
--   $$
--   T_A' = T_A + a_i,\qquad T_B' = \max(T_B, T_A') + b_i,\qquad T_C' = \max(T_C, T_B') + c_i .
--   $$
--   3. A **full sequence** is a permutation $\sigma$ of the jobs, $\sigma(k)$ being the job in position $k$. Its **makespan** is the time machine $C$ finishes the last job of the as-soon-as-possible schedule of $\sigma$, i.e. $\mathrm{TIMEC}$ after all $n$ positions.
--   4. A full sequence $\sigma$ **begins with** $J_r$ when $\sigma(k)$ is the $k$-th job of $J_r$ for every position $k < r$.
--
--   These are the objects every statement of the mission is phrased in. The makespan is taken from Johnson's as-soon-as-possible schedule (the referenced definition `asapSchedule`), and the node attributes follow the same recursion, so for a node $J_r$ with which $\sigma$ begins, $(\mathrm{TIMEA},\mathrm{TIMEB},\mathrm{TIMEC})(J_r)$ is Johnson's completion triple of $\sigma$ after $r$ positions.
--
--   **Formalization Note** A node is a `List (Fin n)`; nothing in the type forces it to be duplicate-free, but every node created by the procedure, and every list that a permutation begins with, is. The paper restricts attention to permutation schedules by citing Johnson (p. 401); the makespan is defined only for those. No sign condition is imposed on the processing times.
-- source:
--   Ignall and Schrage, Application of the branch and bound technique to some flow-shop scheduling problems, Oper. Res. 13 (1965), p. 400 (makespan) and p. 401, "Flowshop Problems as Trees" and "A Lower Bound for the Makespan of All Nodes Emanating from a Given Node" (J_r, J̄_r, TIMEA, TIMEB, TIMEC)

import Mathlib
import Definitions.Def_JohnsonFlowShop_ThreeStage_asapSchedule

namespace IgnallSchrage.Makespan

/-- The machine completion triple after one more job: from `(TA, TB, TC)` and job `i`,
machine A finishes at `TA + a i`, machine B at `max TB (TA + a i) + b i`, machine C at
`max TC (that B time) + c i`. This is exactly the step of
`JohnsonFlowShop.ThreeStage.asapDone`. -/
def appendJob {n : ℕ} (a b c : Fin n → ℝ) (t : ℝ × ℝ × ℝ) (i : Fin n) : ℝ × ℝ × ℝ :=
  let d₁ := t.1 + a i
  let d₂ := max t.2.1 d₁ + b i
  (d₁, d₂, max t.2.2 d₂ + c i)

/-- `times a b c J = (TIMEA(J), TIMEB(J), TIMEC(J))` for a node `J` (a partial sequence, the
list of the jobs scheduled so far, in order): the times at which machines A, B and C finish the
last of the jobs of `J` when they are processed in the order of `J`, as early as possible,
starting from time `0`. For `J = []` it is `(0, 0, 0)`. Whenever `J` is the list of the first
`r` positions of an order `σ` (`J = (List.ofFn σ).take r`), `times a b c J` coincides with
Johnson's `JohnsonFlowShop.ThreeStage.asapDone a b c σ r`, since both apply `appendJob`
position by position. -/
def times {n : ℕ} (a b c : Fin n → ℝ) (J : List (Fin n)) : ℝ × ℝ × ℝ :=
  J.foldl (appendJob a b c) (0, 0, 0)

/-- `unscheduled J` is the set `J̄` of jobs that have not been assigned a position in the
partial sequence `J`. -/
def unscheduled {n : ℕ} (J : List (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun j => j ∉ J)

/-- The makespan of a full sequence `σ` (`σ k` = job in position `k`): the time machine C
finishes the last job, `TIMEC` after all `n` positions of Johnson's as-soon-as-possible
schedule. -/
def makespan {n : ℕ} (a b c : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) : ℝ :=
  (JohnsonFlowShop.ThreeStage.asapDone a b c σ n).2.2

/-- The full sequence `σ` begins with the partial sequence `J`: `J` is a prefix of the list
`[σ 0, σ 1, …, σ (n-1)]`, i.e. `σ k = J[k]` for every position `k < J.length`. -/
def BeginsWith {n : ℕ} (σ : Equiv.Perm (Fin n)) (J : List (Fin n)) : Prop :=
  J <+: List.ofFn σ

end IgnallSchrage.Makespan


