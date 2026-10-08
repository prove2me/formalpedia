-- Prove2me | Definitions.Def_TwoAgentSched_ParetoTotal_Model
-- name    : TwoAgentSched_ParetoTotal_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T08:29:06.881574+00:00
-- url     : https://prove2.me/theorems/1eabeabf-3cc3-43ac-85b7-a3e7687cc767
-- title:
--   §3 and §11.2: two agents on one machine, total completion time of A, maximum cost of B, the problem 1‖ΣC^A_i : f^B_max ≤ Q, and the SPT order of the A-jobs
-- statement:
--   The two-agent single-machine model of Agnetis, Mirchandani, Pacciarelli and Pacifici (2004, §3), specialised to agent $A$'s total completion time against agent $B$'s maximum cost, with the order notions used in §11.2.
--
--   Agent $A$ owns the jobs $J^A_1,\dots,J^A_{n_A}$ and agent $B$ owns $J^B_1,\dots,J^B_{n_B}$; job $J_j$ has processing time $p_j$. All jobs are released at time $0$ and processed one at a time on a single machine. Since every objective is regular, a schedule $\sigma$ is a **sequence** of all $n_A+n_B$ jobs, processed in that order from time $0$ without idle time; $C_j(\sigma)$ is the completion time of $J_j$, the sum of the processing times of $J_j$ and of the jobs before it.
--
--   1. The **total completion time of agent $A$** is $\sum_{h=1}^{n_A} C^A_h(\sigma)$.
--   2. Each $B$-job has a cost function $f^B_k$ of its completion time, and the **maximum cost of agent $B$** is
--   $$f^B_{\max}(\sigma)=\max_{k=1,\dots,n_B} f^B_k\bigl(C^B_k(\sigma)\bigr),$$
--   defined when $n_B\ge 1$.
--   3. Given a bound $Q$, a schedule is **feasible** for $1\|\sum C^A_i : f^B_{\max}\le Q$ if $f^B_k(C^B_k(\sigma))\le Q$ for every $B$-job $k$; the instance is **feasible** if some feasible schedule exists; a schedule is **optimal** if it is feasible and no feasible schedule has a smaller $\sum C^A_h$.
--   4. The $A$-jobs of $\sigma$ **follow the SPT order** if, whenever $J^A_h$ comes before $J^A_{h'}$ in $\sigma$, either $p^A_h<p^A_{h'}$, or $p^A_h=p^A_{h'}$ and $h<h'$. This fixes the relative order of the $A$-jobs completely: shortest processing time first, equal lengths by index.
--   5. A $B$-job $J^B_k$ **precedes** an $A$-job $J^A_h$ in $\sigma$ if it comes earlier in the sequence.
--
--   These are the objects Lemmas 5.4, 11.4 and 11.5 of the paper are stated about. Items 1–3 (the job type, $\sum C^A_h$, $f^B_{\max}$, feasibility, optimality and nondominance) are the shared definitions `TwoAgentSched.MaxMax.Model` and `TwoAgentSched.TotalMax.Model` of this series, which this file imports; it declares items 4 and 5 (`AFollowsSPT`, `BPrecedesA`).
--
--   **Formalization Note** Jobs are `Fin nA ⊕ Fin nB` (`Sum.inl h` is $J^A_{h+1}$, `Sum.inr k` is $J^B_{k+1}$, 0-based). A schedule is a duplicate-free list of all jobs, and completion times come from the published sequence model `MooreLateJobs.Shared.completionTime`. Processing times and $Q$ are real numbers (the paper's $Q$ is an integer; nothing depends on that). Feasibility is stated job by job, which needs no nonemptiness; $f^B_{\max}$ is a `Finset.sup'` and carries the hypothesis $0<n_B$. The paper says only that the $A$-jobs are "SPT ordered"; the tie-break by index is added so that two optimal schedules order identical $A$-jobs the same way, which Lemmas 11.4 and 11.5 need.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), pp. 231–232, §3 (objective functions, CP, feasible instance); p. 240, §11.2 (SPT order of the A-jobs, "k precedes j")

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_TwoAgentSched_MaxMax_Model
import Definitions.Def_TwoAgentSched_TotalMax_Model

namespace TwoAgentSched.ParetoTotal

/-- The A-jobs of `l` appear in the fixed SPT order (§11.2, p. 240: "the A-jobs are always SPT
ordered"): whenever an A-job `J^A_h` comes before an A-job `J^A_{h'}` in `l`, either
`p^A_h < p^A_{h'}`, or `p^A_h = p^A_{h'}` and `h < h'`. Ties between A-jobs of equal length are
broken by index, so on a schedule of all jobs this fixes the order of the A-jobs completely: it
is the enumeration of the A-jobs by nondecreasing processing time, ties by index. -/
def AFollowsSPT {nA nB : ℕ} (p : TwoAgentSched.MaxMax.Job nA nB → ℝ) (l : List (TwoAgentSched.MaxMax.Job nA nB)) : Prop :=
  l.Pairwise (fun x y => ∀ h h' : Fin nA, x = Sum.inl h → y = Sum.inl h' →
    p (Sum.inl h) < p (Sum.inl h') ∨ (p (Sum.inl h) = p (Sum.inl h') ∧ h < h'))

/-- The B-job `J^B_k` precedes the A-job `J^A_h` in the sequence `l`: its position in `l` is
smaller. (On a schedule of all jobs both jobs occur, exactly once.) -/
def BPrecedesA {nA nB : ℕ} (l : List (TwoAgentSched.MaxMax.Job nA nB)) (k : Fin nB) (h : Fin nA) : Prop :=
  l.idxOf (Sum.inr k : TwoAgentSched.MaxMax.Job nA nB) < l.idxOf (Sum.inl h : TwoAgentSched.MaxMax.Job nA nB)

end TwoAgentSched.ParetoTotal


