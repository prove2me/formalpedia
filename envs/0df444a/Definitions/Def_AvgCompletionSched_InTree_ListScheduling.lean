-- Prove2me | Definitions.Def_AvgCompletionSched_InTree_ListScheduling
-- name    : AvgCompletionSched_InTree_ListScheduling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T20:08:12.804656+00:00
-- url     : https://prove2.me/theorems/71ae99c5-ada1-4ae5-b868-c5cd372f090f
-- title:
--   Graham's list scheduling on $m$ machines from a list
-- statement:
--   Fix an instance, a number $m$ of machines, a list $\pi$ of the jobs and a feasible $m$-machine schedule $G$ with start times $S_j$ and completion times $C_j$.
--
--   A job $j$ is **ready** at time $t$ if every predecessor $i\prec j$ has completed by then, $C_i\le t$. All machines are **busy** at $t$ if every machine is processing some job $k$ at $t$, that is $S_k\le t<C_k$.
--
--   $G$ is a **list schedule** for $\pi$ (Graham's list scheduling: whenever a machine is free, start the first ready job of the list on it, footnote 3) if
--
--   1. (no unforced idleness) whenever a job $j$ is ready at a time $t\ge 0$ with $t<S_j$, all $m$ machines are busy at $t$;
--   2. (list priority) whenever a job $l$ starts at time $S_l$ and a job $j$ with $S_j>S_l$ is ready at time $S_l$, the job $l$ precedes $j$ in $\pi$.
--
--   This is the algorithm analyzed in §4.4: "the standard list scheduling algorithm which starts with an ordering on the jobs (the list) and greedily schedules each successive job in the list at the earliest possible time". Rules 1 and 2 determine Graham's schedule up to the labelling of machines and are exactly the two properties the proof of Lemma 4.16 uses.
--
--   **Formalization Note** The algorithm is specified by these two properties rather than by an event-driven simulation; the mission contains a separate theorem asserting that such a schedule exists for every precedence-respecting list, so statements about list schedules are not vacuous. Several jobs may start simultaneously; ties are not restricted beyond rule 2.
-- source:
--   Chekuri, Motwani, Natarajan, Stein, Approximation Techniques for Average Completion Time Scheduling, SIAM J. Comput. 31(1), 2001, p. 158, footnote 3 (list scheduling = the first available job in the list is scheduled when a machine is free); p. 162, §4.4 (standard list scheduling) and proof of Lemma 4.16

import Mathlib
import Definitions.Def_AvgCompletionSched_InTree_Model

namespace AvgCompletionSched.InTree

variable {n m : ℕ}

/-- Job `j` is ready at time `t` in the schedule `G`: every predecessor of `j` has completed by
time `t` (there are no release dates). -/
def IsReady {I : Instance n} (G : Schedule I m) (j : Fin n) (t : ℝ) : Prop :=
  ∀ i, I.prec i j → G.C i ≤ t

/-- All `m` machines are busy at time `t` in the schedule `G`: every machine `μ` is processing
some job `k` at time `t`, i.e. `S_k ≤ t < C_k`. -/
def AllBusy {I : Instance n} (G : Schedule I m) (t : ℝ) : Prop :=
  ∀ μ : Fin m, ∃ k, G.M k = μ ∧ G.S k ≤ t ∧ t < G.C k

/-- `G` is a list schedule for the list `π` in the sense of footnote 3 (p. 158) and §4.4
(p. 162): whenever a machine is free, the first ready job in the list is started on it
(Graham's list scheduling). Up to the labelling of machines this is captured by two rules:
1. no unforced idleness: if a job `j` is ready at time `t ≥ 0` but has not started yet
   (`t < S_j`), then all `m` machines are busy at `t`;
2. list priority: if a job `l` starts at time `S_l` and another job `j` that starts later is
   already ready at `S_l`, then `l` comes before `j` in the list. -/
def IsListSchedule (I : Instance n) (π : Fin n ≃ Fin n) (G : Schedule I m) : Prop :=
  (∀ j (t : ℝ), 0 ≤ t → t < G.S j → IsReady G j t → AllBusy G t) ∧
  (∀ l j, G.S l < G.S j → IsReady G j (G.S l) → π.symm l < π.symm j)

end AvgCompletionSched.InTree


