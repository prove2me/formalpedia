-- Prove2me | Definitions.Def_AvgCompletionSched_DelayList_Model
-- name    : AvgCompletionSched_DelayList_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T19:59:31.947733+00:00
-- url     : https://prove2.me/theorems/e0b0409c-ca57-44a5-94e0-4c912ee57010
-- title:
--   Weighted completion time scheduling with release dates and precedence: instances, schedules, critical paths $\kappa_j$, lists
-- statement:
--   This file sets up the model of §4 of Chekuri, Motwani, Natarajan and Stein: nonpreemptive scheduling with release dates and precedence constraints, minimizing the sum of weighted completion times.
--
--   **Instance.** There are $n$ jobs $J_0,\dots,J_{n-1}$. Job $J_j$ has processing time $p_j>0$, release date $r_j\ge 0$ and weight $w_j>0$. The precedence constraints form a strict partial order $\prec$ on the jobs ($i\prec j$: job $i$ must complete before job $j$ starts); the directed acyclic graph of the paper is represented by its transitive closure. The number $m$ of machines is not part of the instance.
--
--   **Schedules.** A feasible nonpreemptive schedule on $m$ machines assigns each job a start time $S_j$ and a machine $M_j$; job $J_j$ runs without interruption on $M_j$ during $[S_j,S_j+p_j)$, with
--   $$S_j\ge r_j,\qquad M_i=M_j,\ i\ne j\ \Rightarrow\ S_i+p_i\le S_j\ \text{or}\ S_j+p_j\le S_i,\qquad i\prec j\ \Rightarrow\ S_i+p_i\le S_j .$$
--   Its completion times are $C_j=S_j+p_j$ and its value is $\sum_j w_jC_j$. A one-machine schedule is a schedule with $m=1$.
--
--   **Critical paths (Definition 4.1).** For a job $j$ with no predecessors $\kappa_j=p_j+r_j$; otherwise
--   $$\kappa_j=p_j+\max\Bigl\{\max_{i\prec j}\kappa_i,\ r_j\Bigr\}.$$
--
--   **Lists.** A list is an ordering $\pi$ of the jobs ($\pi(k)$ is the $k$-th job). It obeys the precedence constraints if $i\prec j$ implies that $i$ comes earlier than $j$ (footnote 2). It is the completion order of a one-machine schedule $S^1$ if it lists the jobs in nondecreasing order of their completion times $C^1_j$ in $S^1$.
--
--   These objects are used by every statement of the mission.
--
--   **Formalization Note** Jobs are `Fin n`, machines `Fin m`, times real. The recursion defining $\kappa$ is well-founded recursion on $\prec$ (a finite strict partial order); the file contains the one-line proof of this well-foundedness. Taking the transitive closure of the DAG does not change $\kappa$, feasibility, or readiness, because processing times are positive.
-- source:
--   Chekuri, Motwani, Natarajan, Stein, Approximation Techniques for Average Completion Time Scheduling, SIAM J. Comput. 31(1), 2001, pp. 146–147 §1 (model, footnote 1); p. 157 §4 (DAG); p. 158 (notation $S^m$, $C^m$, $p(A)$; Definition 4.1; footnote 2; the one-machine schedule taken as a list)

import Mathlib

namespace AvgCompletionSched.DelayList

/-- An instance of weighted completion time scheduling with release dates and precedence
constraints (Chekuri–Motwani–Natarajan–Stein 2001, §1, pp. 146–147, and §4, pp. 157–158):
`n` jobs `0, …, n-1`; job `j` has processing time `p j > 0`, release date `r j ≥ 0` and weight
`w j > 0`. The precedence constraints are given by a strict partial order `prec` on the jobs
(`prec i j` means `i ≺ j`: job `i` must be completed before job `j` starts); the DAG of the paper
is represented by its transitive closure. The number of machines is not part of the instance. -/
structure Instance (n : ℕ) where
  /-- processing times -/
  p : Fin n → ℝ
  /-- release dates -/
  r : Fin n → ℝ
  /-- weights -/
  w : Fin n → ℝ
  /-- precedence relation: `prec i j` means `i ≺ j` -/
  prec : Fin n → Fin n → Prop
  p_pos : ∀ j, 0 < p j
  r_nonneg : ∀ j, 0 ≤ r j
  w_pos : ∀ j, 0 < w j
  prec_irrefl : ∀ j, ¬ prec j j
  prec_trans : ∀ i j k, prec i j → prec j k → prec i k

variable {n : ℕ}

open Classical in
/-- The predecessors of job `j`: the jobs `i` with `i ≺ j`. -/
noncomputable def Instance.preds (I : Instance n) (j : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun i => I.prec i j

/-- The precedence relation of an instance is well founded (a finite strict partial order). -/
theorem Instance.prec_wf (I : Instance n) : WellFounded I.prec :=
  @Finite.wellFounded_of_trans_of_irrefl _ _ I.prec ⟨I.prec_trans⟩ ⟨I.prec_irrefl⟩

/-- Definition 4.1 (p. 158): the critical-path length `κ_j`, defined recursively along the
precedence order. For a job `j` with no predecessors `κ_j = p_j + r_j`; otherwise
`κ_j = p_j + max {max_{i ≺ j} κ_i, r_j}`. -/
noncomputable def kappa (I : Instance n) : Fin n → ℝ :=
  I.prec_wf.fix fun j IH =>
    if h : (I.preds j).Nonempty then
      I.p j + max ((I.preds j).attach.sup' (Finset.attach_nonempty_iff.mpr h)
        fun i => IH i.1 (by simpa [Instance.preds] using i.2)) (I.r j)
    else I.p j + I.r j

/-- A feasible nonpreemptive schedule of the instance on `m` machines: job `j` runs without
interruption on machine `M j` during `[S j, S j + p j)`; it does not start before its release
date; two different jobs on the same machine do not overlap; and if `i ≺ j` then `j` starts no
earlier than `i` completes. A one-machine schedule is a schedule with `m = 1`. -/
structure Schedule (I : Instance n) (m : ℕ) where
  /-- start times -/
  S : Fin n → ℝ
  /-- machine assignment -/
  M : Fin n → Fin m
  released : ∀ j, I.r j ≤ S j
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

/-- The list `π` is the one-machine schedule `S1` taken as a list (p. 158): the jobs in order of
their completion times in `S1`. -/
def IsCompletionOrder {I : Instance n} (S1 : Schedule I 1) (π : Fin n ≃ Fin n) : Prop :=
  ∀ k l : Fin n, k ≤ l → S1.C (π k) ≤ S1.C (π l)

end AvgCompletionSched.DelayList


