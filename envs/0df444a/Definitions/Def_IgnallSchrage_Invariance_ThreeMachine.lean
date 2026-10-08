-- Prove2me | Definitions.Def_IgnallSchrage_Invariance_ThreeMachine
-- name    : IgnallSchrage_Invariance_ThreeMachine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:32:54.607631+00:00
-- url     : https://prove2.me/theorems/6e7b4321-b7fb-45e1-a88b-e29951bdbd27
-- title:
--   Three machines — TIMEA/TIMEB/TIMEC, the makespan and the lower bound $LB(J_r)$ of p. 401
-- statement:
--   The three-machine makespan problem. Job $i$ has processing times $a_i$, $b_i$, $c_i$ on machines $A$, $B$, $C$, and every job visits $A$, then $B$, then $C$.
--
--   1. For a node $J_r$, $\mathrm{TIMEA}(J_r)$, $\mathrm{TIMEB}(J_r)$, $\mathrm{TIMEC}(J_r)$ are the times at which machines $A$, $B$, $C$ finish the last job of $J_r$. The jobs are processed in the order of $J_r$, each operation as early as possible, from time $0$. Starting from $(0,0,0)$, appending job $i$ to $(T_A,T_B,T_C)$ gives
--   $$
--   T_A' = T_A + a_i,\qquad T_B' = \max(T_B, T_A') + b_i,\qquad T_C' = \max(T_C, T_B') + c_i .
--   $$
--   2. The **makespan** of a full sequence $\sigma$ ($\sigma(k)$ the job in position $k$) is the time machine $C$ finishes the last job of Johnson's as-soon-as-possible schedule of $\sigma$.
--   3. The **lower bound** of p. 401 of a node $J_r$ is
--   $$
--   LB(J_r)=\max\Big[\mathrm{TIMEA}(J_r)+\sum_{\bar J_r}a_i+\min_{\bar J_r}(b_i+c_i),\ \mathrm{TIMEB}(J_r)+\sum_{\bar J_r}b_i+\min_{\bar J_r}c_i,\ \mathrm{TIMEC}(J_r)+\sum_{\bar J_r}c_i\Big].
--   $$
--
--   These are the paper's objects for the three-machine problem. The node attributes follow the recursion of Johnson's schedule, so for a $\sigma$ whose first $r$ positions are $J_r$, the triple $(\mathrm{TIMEA},\mathrm{TIMEB},\mathrm{TIMEC})(J_r)$ is Johnson's completion triple after $r$ positions.
--
--   **Formalization Note** The bound is meant for nodes with $\bar J_r$ nonempty ($r\le n-1$), the only ones the procedure ranks. Minima use the `minOver` of the definition `Node`. This file repeats objects of mission 1 of this series (the drafts cannot import one another).
-- source:
--   Ignall and Schrage, Application of the branch and bound technique to some flow-shop scheduling problems, Oper. Res. 13 (1965), p. 400 (makespan) and p. 401, "A Lower Bound for the Makespan of All Nodes Emanating from a Given Node" (TIMEA, TIMEB, TIMEC, LB(J_r))

import Mathlib
import Definitions.Def_JohnsonFlowShop_ThreeStage_asapSchedule
import Definitions.Def_IgnallSchrage_Invariance_Node
import Definitions.Def_IgnallSchrage_Makespan_Node

namespace IgnallSchrage.Invariance

/-- The machine completion triple after one more job: from `(TA, TB, TC)` and job `i`,
machine A finishes at `TA + a i`, machine B at `max TB (TA + a i) + b i`, machine C at
`max TC (that B time) + c i`. This is exactly the step of
`JohnsonFlowShop.ThreeStage.asapDone`. -/
def appendJob3 {n : ℕ} (a b c : Fin n → ℝ) (t : ℝ × ℝ × ℝ) (i : Fin n) : ℝ × ℝ × ℝ :=
  let d₁ := t.1 + a i
  let d₂ := max t.2.1 d₁ + b i
  (d₁, d₂, max t.2.2 d₂ + c i)

/-- `times3 a b c J = (TIMEA(J), TIMEB(J), TIMEC(J))` for a node `J` (a partial sequence, the
list of the jobs scheduled so far, in order): the times at which machines A, B and C finish the
last of the jobs of `J` when they are processed in the order of `J`, as early as possible,
starting from time `0` (p. 401). For `J = []` it is `(0, 0, 0)`. Whenever `J` is the list of the
first `r` positions of an order `σ`, `times3 a b c J` coincides with Johnson's
`JohnsonFlowShop.ThreeStage.asapDone a b c σ r`, since both apply `appendJob3` position by
position. -/
def times3 {n : ℕ} (a b c : Fin n → ℝ) (J : List (Fin n)) : ℝ × ℝ × ℝ :=
  J.foldl (appendJob3 a b c) (0, 0, 0)

/-- The three-machine lower bound of Ignall and Schrage (p. 401) of a node `J = J_r`, with
`J̄_r` its set of unscheduled jobs:
`LB(J_r) = max [ TIMEA(J_r) + Σ_{J̄_r} a_i + min_{J̄_r} (b_i + c_i),
                 TIMEB(J_r) + Σ_{J̄_r} b_i + min_{J̄_r} c_i,
                 TIMEC(J_r) + Σ_{J̄_r} c_i ]`.
It is meant for nodes with `J̄_r` nonempty (`r ≤ n - 1`), where the minima are genuine minima;
the procedure never evaluates it at a node with `J̄_r = ∅`. -/
def lowerBound3 {n : ℕ} (a b c : Fin n → ℝ) (J : List (Fin n)) : ℝ :=
  let t := times3 a b c J
  let U := IgnallSchrage.Makespan.unscheduled J
  max (t.1 + ∑ i ∈ U, a i + IgnallSchrage.Makespan.minOver U (fun i => b i + c i))
    (max (t.2.1 + ∑ i ∈ U, b i + IgnallSchrage.Makespan.minOver U c)
      (t.2.2 + ∑ i ∈ U, c i))

end IgnallSchrage.Invariance


