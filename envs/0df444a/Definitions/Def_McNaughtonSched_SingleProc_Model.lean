-- Prove2me | Definitions.Def_McNaughtonSched_SingleProc_Model
-- name    : McNaughtonSched_SingleProc_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:58:59.788178+00:00
-- url     : https://prove2.me/theorems/6b256e68-6c7e-44a4-bea4-0773090f1d72
-- title:
--   Single-processor schedules with splitting, completion times and linear deadline loss
-- statement:
--   This file fixes the model of §2 of McNaughton (1959): $m$ tasks $(1),\dots,(m)$ are to be processed on a single processor, starting at the present, time $0$. Task $(i)$ needs $a_i$ units of processing time, has a deadline $d_i$ and a penalty rate $p_i$. If $(i)$ is completed at time $C_i \le d_i$ there is no loss; otherwise the loss on $(i)$ is $p_i x$, where $x = C_i - d_i$ is the number of units of time from the deadline to the completion. The ratio $r_i = p_i/a_i$ orders the tasks.
--
--   **Schedules and splitting.** A task may be split into any finite number of parts. A **schedule** is therefore a finite list of **pieces**, each consisting of a task, a start time and a stop time. A schedule is **feasible** for the processing times $a$ when
--
--   1. every piece satisfies $0 \le \text{start} \le \text{stop}$;
--   2. no two pieces overlap in time (one processor; touching intervals are allowed);
--   3. for each task $(i)$ the lengths of its pieces add up to exactly $a_i$.
--
--   **Completion and loss.** The completion time $C_i(S)$ of task $(i)$ in $S$ is the largest stop time among its pieces. The loss on $(i)$ at completion time $t$ is
--
--   $$
--   \ell_i(t) = p_i \cdot \max(0,\ t - d_i),
--   $$
--
--   and the total loss of $S$ is $c(S) = \sum_{i=1}^m \ell_i(C_i(S))$.
--
--   **Unsplit sequenced schedules.** A schedule has **no split task** when every task is processed in exactly one piece. For an order $\sigma$ of the tasks ($\sigma(k)$ is the task in position $k$), the schedule without splits and without unused time puts $\sigma(k)$ on the interval $\bigl[\sum_{l<k} a_{\sigma(l)},\ \sum_{l\le k} a_{\sigma(l)}\bigr]$. The order is **in order of decreasing $r_i$** when an earlier position never has a smaller ratio: $k \le l$ implies $r_{\sigma(l)} \le r_{\sigma(k)}$.
--
--   These objects are shared by all statements of the mission: Theorems 2.1–2.4 and the steps of their proofs.
--
--   **Formalization Note** Tasks $(1),\dots,(m)$ and positions in an order are the $0$-based indices of `Fin m`; times, lengths, deadlines and penalties are real numbers. The completion time of a task with no piece is $0$ (the empty maximum); feasibility together with $a_i > 0$ excludes that case. The loss $p_i\max(0,t-d_i)$ equals the introduction's $\max(0, p(t-d))$ whenever $p_i \ge 0$. "No split" counts pieces, so two abutting pieces of one task count as a split; this only makes existence of an unsplit optimum a stronger claim. "Decreasing" is read as non-increasing, with ties in any order.
-- source:
--   McNaughton, Scheduling with Deadlines and Loss Functions, Management Science 6(1), 1959, p. 4, §2 (model, loss p_i x, r_i = p_i/a_i, splitting); p. 2 (loss function max(0, p(t − d)))

import Mathlib

namespace McNaughtonSched.SingleProc

/-- One piece of work on the single processor: task `task` is processed during the time
interval from `start` to `stop`. Tasks (1), …, (m) of McNaughton (1959), §2, p. 4, are the
zero-based indices of `Fin m`. A task done in several parts ("split", p. 4) has several
pieces. -/
structure Piece (m : ℕ) where
  task : Fin m
  start : ℝ
  stop : ℝ

/-- A schedule for the single processor is a finite list of pieces; a task "may be split in
any number of parts" (p. 4), finitely many. -/
abbrev Schedule (m : ℕ) := List (Piece m)

variable {m : ℕ}

/-- Two pieces occupy disjoint time intervals (touching endpoints allowed). -/
def Piece.Disjoint (g h : Piece m) : Prop := g.stop ≤ h.start ∨ h.stop ≤ g.start

/-- The total processing time that schedule `S` gives to task `i`: the summed lengths of its
pieces. -/
noncomputable def processed (S : Schedule m) (i : Fin m) : ℝ :=
  ((S.filter fun g => g.task = i).map fun g => g.stop - g.start).sum

/-- A feasible schedule for processing times `a`: every piece lies in `[0, ∞)` (time `0` is
"the present", p. 4) and has `start ≤ stop`; no two pieces overlap in time (one processor);
and every task `i` receives exactly `a i` units of processing time. -/
def IsFeasible (a : Fin m → ℝ) (S : Schedule m) : Prop :=
  (∀ g ∈ S, 0 ≤ g.start ∧ g.start ≤ g.stop) ∧
    S.Pairwise Piece.Disjoint ∧
    ∀ i, processed S i = a i

/-- The completion time of task `i` in `S`: the latest stop time of one of its pieces
(`0` if it has none, which feasibility with `a i > 0` excludes). -/
noncomputable def completion (S : Schedule m) (i : Fin m) : ℝ :=
  ((S.filter fun g => g.task = i).map Piece.stop).foldr max 0

/-- The loss on task `i` when it is completed at time `t`: `p_i x`, where `x` is the number
of units of time from the deadline `d_i` to the completion, and no loss if the task is
finished at or before `d_i` (p. 4). -/
noncomputable def taskLoss (p d : Fin m → ℝ) (i : Fin m) (t : ℝ) : ℝ :=
  p i * max 0 (t - d i)

/-- The total loss of schedule `S` with penalties `p` and deadlines `d`. -/
noncomputable def totalLoss (p d : Fin m → ℝ) (S : Schedule m) : ℝ :=
  ∑ i, taskLoss p d i (completion S i)

/-- No task is split: every task is processed in exactly one piece. -/
def NoSplit (S : Schedule m) : Prop :=
  ∀ i, (S.filter fun g => g.task = i).length = 1

/-- The unsplit schedule without unused time that processes the tasks in the order `σ`
(`σ k` is the task in position `k`, positions being the zero-based indices of `Fin m`): task `σ k` runs from
`∑_{l<k} a (σ l)` to `∑_{l≤k} a (σ l)`. -/
noncomputable def seqSchedule (a : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) : Schedule m :=
  List.ofFn fun k : Fin m =>
    { task := σ k
      start := ∑ l ∈ Finset.univ.filter (fun l : Fin m => l < k), a (σ l)
      stop := ∑ l ∈ Finset.univ.filter (fun l : Fin m => l ≤ k), a (σ l) }

/-- The order `σ` lists the tasks in order of decreasing (non-increasing) ratio
`r_i = p_i / a_i` (p. 4): an earlier position never has a smaller ratio. Ties are allowed in
any order. -/
def InRatioOrder (a p : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) : Prop :=
  ∀ k l : Fin m, k ≤ l → p (σ l) / a (σ l) ≤ p (σ k) / a (σ k)

end McNaughtonSched.SingleProc


