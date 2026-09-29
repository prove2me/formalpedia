-- Prove2me | Definitions.Def_AvgCompletionSched_InTree_Model
-- name    : AvgCompletionSched_InTree_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T20:07:39.006271+00:00
-- url     : https://prove2.me/theorems/12de8713-0f6d-4779-8371-ca3870aeda13
-- title:
--   In-tree scheduling without release dates: instances, schedules, critical paths $\kappa_j$, one-machine schedules
-- statement:
--   This file sets up the model of §4.4 of Chekuri, Motwani, Natarajan and Stein: nonpreemptive scheduling of weighted jobs on $m$ identical machines under in-tree precedence constraints and without release dates, minimizing the sum of weighted completion times.
--
--   **Instance.** There are $n$ jobs $J_0,\dots,J_{n-1}$. Job $J_j$ has processing time $p_j>0$ and weight $w_j>0$, and is available at time $0$. The precedence constraints form an in-tree (more generally an in-forest): every job $j$ has at most one immediate successor $\operatorname{succ}(j)$, and following immediate successors never returns to the starting job. The precedence relation $i\prec j$ holds when $j$ is reached from $i$ by following immediate successors one or more times.
--
--   **Critical paths (Definition 4.1 with $r\equiv 0$).** For a job $j$ with no predecessors $\kappa_j=p_j$; otherwise
--   $$\kappa_j=p_j+\max_{i\prec j}\kappa_i .$$
--
--   **Schedules.** A feasible nonpreemptive schedule on $m$ machines assigns each job a start time $S_j\ge 0$ and a machine $M_j$; job $J_j$ runs without interruption on $M_j$ during $[S_j,S_j+p_j)$, with
--   $$M_i=M_j,\ i\ne j\ \Rightarrow\ S_i+p_i\le S_j\ \text{or}\ S_j+p_j\le S_i,\qquad i\prec j\ \Rightarrow\ S_i+p_i\le S_j .$$
--   Its completion times are $C_j=S_j+p_j$ and its value is $\sum_j w_jC_j$.
--
--   **Lists and one-machine schedules.** A list is an ordering $\pi$ of the jobs ($\pi(k)$ is the $k$-th job); it obeys the precedence constraints if $i\prec j$ implies that $i$ comes earlier than $j$ (footnote 2). The one-machine schedule $S^1$ of a list processes the jobs in list order without idle time, so
--   $$C^1_j=\sum_{k\le \pi^{-1}(j)} p_{\pi(k)},\qquad C^1=\sum_j w_jC^1_j .$$
--   A list is an optimal one-machine schedule if it obeys the precedence constraints and no precedence-respecting list has a smaller $C^1$.
--
--   These objects are used by every statement of the mission.
--
--   **Formalization Note** Jobs are `Fin n`, machines `Fin m`, times real. The recursion defining $\kappa$ is well-founded recursion on $\prec$; the file contains the one-line proof of this well-foundedness. Because there are no release dates and processing times are positive, inserting idle time into a one-machine schedule only increases completion times, so one-machine schedules are represented by their (idle-free) order; the one-machine optimum is taken over precedence-respecting orders.
-- source:
--   Chekuri, Motwani, Natarajan, Stein, Approximation Techniques for Average Completion Time Scheduling, SIAM J. Comput. 31(1), 2001, pp. 146–147 §1 (model, footnote 1); p. 158 (notation $S^m$, $C^m$; Definition 4.1; footnote 2); p. 162 §4.4 (in-tree precedence without release dates; the optimal one-machine schedule as the list)

import Mathlib

namespace AvgCompletionSched.InTree

/-- An instance of weighted completion time scheduling with in-tree precedence constraints and
no release dates (Chekuri–Motwani–Natarajan–Stein 2001, §1, pp. 146–147, and §4.4, p. 162):
`n` jobs `0, …, n-1`; job `j` has processing time `p j > 0` and weight `w j > 0`; every job is
available at time `0`. The in-tree (more generally in-forest) precedence structure is given by
the unique immediate successor `succ j` of each job (`none` if `j` has no successor): in an
in-tree a node has at most one immediate successor. The successor graph has no cycles. The
number of machines is not part of the instance. -/
structure Instance (n : ℕ) where
  /-- processing times -/
  p : Fin n → ℝ
  /-- weights -/
  w : Fin n → ℝ
  /-- the immediate successor of each job, if any -/
  succ : Fin n → Option (Fin n)
  p_pos : ∀ j, 0 < p j
  w_pos : ∀ j, 0 < w j
  acyclic : ∀ j, ¬ Relation.TransGen (fun a b => succ a = some b) j j

variable {n : ℕ}

/-- The precedence relation `i ≺ j`: `j` is reached from `i` by following immediate successors
one or more times (the transitive closure of the in-tree's edges `i → succ i`). -/
def Instance.prec (I : Instance n) (i j : Fin n) : Prop :=
  Relation.TransGen (fun a b => I.succ a = some b) i j

/-- The precedence relation of an instance is well founded (a finite strict partial order). -/
theorem Instance.prec_wf (I : Instance n) : WellFounded I.prec :=
  @Finite.wellFounded_of_trans_of_irrefl _ _ I.prec
    ⟨fun _ _ _ h₁ h₂ => Relation.TransGen.trans h₁ h₂⟩ ⟨I.acyclic⟩

open Classical in
/-- The predecessors of job `j`: the jobs `i` with `i ≺ j`. -/
noncomputable def Instance.preds (I : Instance n) (j : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun i => I.prec i j

/-- Definition 4.1 (p. 158) with all release dates equal to `0`: the critical-path length
`κ_j`, defined recursively along the precedence order. For a job `j` with no predecessors
`κ_j = p_j`; otherwise `κ_j = p_j + max_{i ≺ j} κ_i`. -/
noncomputable def kappa (I : Instance n) : Fin n → ℝ :=
  I.prec_wf.fix fun j IH =>
    if h : (I.preds j).Nonempty then
      I.p j + (I.preds j).attach.sup' (Finset.attach_nonempty_iff.mpr h)
        fun i => IH i.1 (by simpa [Instance.preds] using i.2)
    else I.p j

/-- A feasible nonpreemptive schedule of the instance on `m` identical machines: job `j` runs
without interruption on machine `M j` during `[S j, S j + p j)`; no job starts before time `0`
(there are no release dates); two different jobs on the same machine do not overlap; and if
`i ≺ j` then `j` starts no earlier than `i` completes. -/
structure Schedule (I : Instance n) (m : ℕ) where
  /-- start times -/
  S : Fin n → ℝ
  /-- machine assignment -/
  M : Fin n → Fin m
  nonneg : ∀ j, 0 ≤ S j
  noOverlap : ∀ i j, M i = M j → i ≠ j → S i + I.p i ≤ S j ∨ S j + I.p j ≤ S i
  precedence : ∀ i j, I.prec i j → S i + I.p i ≤ S j

/-- Completion time `C_j = S_j + p_j` of job `j` in a nonpreemptive schedule. -/
def Schedule.C {I : Instance n} {m : ℕ} (N : Schedule I m) (j : Fin n) : ℝ :=
  N.S j + I.p j

/-- The objective value of a schedule: the sum of weighted completion times `∑_j w_j C_j`. -/
noncomputable def Schedule.wct {I : Instance n} {m : ℕ} (N : Schedule I m) : ℝ :=
  ∑ j, I.w j * N.C j

/-- A list of the jobs, `π k` being the `k`-th job of the list, obeys the precedence constraints
(footnote 2, p. 158): if `i ≺ j` then `i` comes earlier in the list than `j`. -/
def ObeysPrecedence (I : Instance n) (π : Fin n ≃ Fin n) : Prop :=
  ∀ i j, I.prec i j → π.symm i < π.symm j

/-- The idle-free one-machine schedule `S¹` that processes the jobs in the order of the list
`π`: the completion time of job `j` is the total processing time of the jobs up to and
including `j` in the list, `C¹_j = ∑_{k ≤ pos(j)} p_{π k}`. -/
noncomputable def oneMachineC (I : Instance n) (π : Fin n ≃ Fin n) (j : Fin n) : ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k => k ≤ π.symm j), I.p (π k)

/-- The sum of weighted completion times `C¹ = ∑_j w_j C¹_j` of the one-machine schedule in the
order `π`. -/
noncomputable def oneMachineWct (I : Instance n) (π : Fin n ≃ Fin n) : ℝ :=
  ∑ j, I.w j * oneMachineC I π j

/-- `π` is an optimal one-machine schedule: it obeys the precedence constraints, and no
precedence-respecting order has a smaller sum of weighted completion times. (With no release
dates and positive processing times, idle time never helps, so optimal one-machine schedules are
idle-free and determined by their order.) -/
def IsOptimalOneMachine (I : Instance n) (π : Fin n ≃ Fin n) : Prop :=
  ObeysPrecedence I π ∧ ∀ σ : Fin n ≃ Fin n, ObeysPrecedence I σ → oneMachineWct I π ≤ oneMachineWct I σ

end AvgCompletionSched.InTree


