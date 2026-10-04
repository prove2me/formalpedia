-- Prove2me | Definitions.Def_DelayedSWPT_Model_dswpt
-- name    : DelayedSWPT_Model_dswpt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T04:29:08.07897+00:00
-- url     : https://prove2.me/theorems/8e055db3-1d94-4c1e-afc1-12280a9526d9
-- title:
--   The Delayed SWPT online scheduling algorithm
-- statement:
--   **Delayed SWPT** is the following online rule for a single machine, run over the unit time slots $[t, t+1)$, $t = 0, 1, 2, \dots$
--
--   Suppose the machine is available at time $t$. Among the **available** jobs (released, $r_j \le t$, and not yet started) choose a job $j$ with the smallest ratio $p_j / w_j$; in case of ties choose one with the smallest processing time, and if there is still a choice, the one with the smallest index. If $p_j \le t$, job $j$ starts at time $t$ and the machine is busy until $t + p_j$. Otherwise the machine stays idle in $[t, t+1)$ and the choice is made again at $t+1$. If no job is available, the machine also stays idle.
--
--   The priority is the strict order
--
--   $$j \prec k \iff p_j w_k < p_k w_j \ \text{ or } \ \bigl(p_j w_k = p_k w_j \text{ and } (p_j < p_k \text{ or } (p_j = p_k \text{ and } j < k))\bigr).$$
--
--   The resulting start times $\pi_j$ define the **Delayed SWPT schedule** $\pi$. At each time the rule only looks at jobs already released, so it is an online algorithm.
--
--   This is the algorithm whose competitive ratio the mission establishes. The delay "no job $j$ starts before time $p_j$" is what distinguishes it from plain online SWPT, whose competitive ratio is unbounded.
--
--   **Formalization Note** The rule is a discrete-time simulation whose state records the start times assigned so far and the time from which the machine is free. The paper's "do nothing until time $p_j$ or another job is released" is implemented by re-evaluating the choice at each unit time: if no job is released in between, the same job is chosen again. The simulation runs for $\sum_j (r_j + 2p_j) + 1$ slots, after which every job has started. Ratios are compared by cross-multiplication; `select` scans the jobs in index order and returns the $\prec$-least available job. `dswptState` and `dswptChoice` expose the state and the choice at each time; the extended problem (E) uses them to define gap jobs.
-- source:
--   Anderson and Potts, Online Scheduling of a Single Machine to Minimize Total Weighted Completion Time, Math. Oper. Res. 29(3) (2004), p. 688–689, §2 (Delayed SWPT)

import Mathlib
import Definitions.Def_DelayedSWPT_Model_Instance

namespace DelayedSWPT.Model

/-- The Delayed SWPT priority (Anderson and Potts, p. 689): job `j` is preferred to job `k`
when `p_j/w_j < p_k/w_k`, ties broken by the smaller processing time and then by the smaller
index. Ratios are compared by cross-multiplication (`w > 0`). -/
def Prec {n : ℕ} (I : Instance n) (j k : Fin n) : Prop :=
  (I.p j : ℝ) * I.w k < (I.p k : ℝ) * I.w j ∨
    ((I.p j : ℝ) * I.w k = (I.p k : ℝ) * I.w j ∧ (I.p j < I.p k ∨ (I.p j = I.p k ∧ j < k)))

/-- The job of `A` chosen by a priority `prec`: scan the jobs in index order and keep the
current candidate unless the next job of `A` strictly precedes it. For the strict total order
`Prec I` this is the `Prec I`-least job of `A`; it is `none` exactly when `A` is empty.
Only `prec` between members of `A` is ever consulted. -/
def select {n : ℕ} (prec : Fin n → Fin n → Prop) [DecidableRel prec] (A : Finset (Fin n)) :
    Option (Fin n) :=
  (List.finRange n).foldl
    (fun acc k =>
      if k ∈ A then
        (match acc with
         | none => some k
         | some b => if prec k b then some k else some b)
      else acc)
    none

/-- The state of the simulation at the beginning of a unit time slot: the start times assigned
so far (`none` = not yet started) and the time `free` from which the machine is available. -/
structure State (n : ℕ) where
  start : Fin n → Option ℕ
  free : ℕ

/-- Nothing started, machine available from time `0`. -/
def initState (n : ℕ) : State n := ⟨fun _ => none, 0⟩

/-- The jobs available at time `t` in state `s`: released (`r j ≤ t`) and not yet started. -/
def available {n : ℕ} (r : Fin n → ℕ) (s : State n) (t : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => r j ≤ t ∧ s.start j = none)

/-- The job selected at time `t`: if the machine is available (`s.free ≤ t`), the
highest-priority available job (if any); otherwise `none`. It depends only on the jobs with
`r j ≤ t` (online rule). -/
def choice {n : ℕ} (r : Fin n → ℕ) (prec : Fin n → Fin n → Prop) [DecidableRel prec]
    (s : State n) (t : ℕ) : Option (Fin n) :=
  if s.free ≤ t then select prec (available r s t) else none

/-- One unit time slot `[t, t + 1)` of Delayed SWPT: if the selected job `j` has `p j ≤ t`, it
starts at `t` and the machine is busy until `t + p j`; otherwise the machine stays idle during
`[t, t + 1)` and the choice is made afresh at `t + 1`. -/
def step {n : ℕ} (r p : Fin n → ℕ) (prec : Fin n → Fin n → Prop) [DecidableRel prec]
    (t : ℕ) (s : State n) : State n :=
  match choice r prec s t with
  | none => s
  | some j => if p j ≤ t then ⟨Function.update s.start j (some t), t + p j⟩ else s

/-- The state at the beginning of slot `t`, after the slots `0, 1, …` before `t`. -/
def stateAt {n : ℕ} (r p : Fin n → ℕ) (prec : Fin n → Fin n → Prop) [DecidableRel prec] :
    ℕ → State n
  | 0 => initState n
  | t + 1 => step r p prec t (stateAt r p prec t)

/-- The simulation horizon `∑ⱼ (rⱼ + 2pⱼ) + 1`; every job has started before it. -/
def horizon {n : ℕ} (r p : Fin n → ℕ) : ℕ := ∑ j, (r j + 2 * p j) + 1

/-- The state of Delayed SWPT on instance `I` at the beginning of slot `t`. -/
noncomputable def dswptState {n : ℕ} (I : Instance n) (t : ℕ) : State n :=
  @stateAt n I.r I.p (Prec I) (Classical.decRel _) t

/-- The job Delayed SWPT selects at time `t` (`none` if the machine is busy or nothing is
available). -/
noncomputable def dswptChoice {n : ℕ} (I : Instance n) (t : ℕ) : Option (Fin n) :=
  @choice n I.r (Prec I) (Classical.decRel _) (dswptState I t) t

/-- The Delayed SWPT schedule `π` (start times) on instance `I`, read off the simulation at the
horizon. -/
noncomputable def dswpt {n : ℕ} (I : Instance n) (j : Fin n) : ℕ :=
  ((dswptState I (horizon I.r I.p)).start j).getD 0

end DelayedSWPT.Model


