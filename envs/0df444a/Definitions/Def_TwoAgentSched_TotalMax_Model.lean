-- Prove2me | Definitions.Def_TwoAgentSched_TotalMax_Model
-- name    : TwoAgentSched_TotalMax_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T07:38:00.193579+00:00
-- url     : https://prove2.me/theorems/6cfdba3c-e8a2-46fa-8daa-5e70353a6091
-- title:
--   §3 and §5: two agents on one machine, total completion time of A, maximum cost of B, the problem 1‖ΣC^A_i : f^B_max ≤ Q, and nondominated schedules
-- statement:
--   The two-agent single-machine model of Agnetis, Mirchandani, Pacciarelli and Pacifici (2004, §3), specialised to agent A's total completion time against agent B's maximum cost.
--
--   Agent $A$ owns the jobs $J^A_1,\dots,J^A_{n_A}$ and agent $B$ owns $J^B_1,\dots,J^B_{n_B}$; job $J_j$ has processing time $p_j$. All jobs are released at time $0$ and processed one at a time on a single machine. Since every objective is regular, a schedule $\sigma$ is a **sequence** of all $n_A+n_B$ jobs, processed in that order from time $0$ without idle time; $C_j(\sigma)$ is the completion time of $J_j$, i.e. the sum of the processing times of $J_j$ and of the jobs before it.
--
--   1. The **total completion time of agent $A$** is $\sum_{h=1}^{n_A} C^A_h(\sigma)$.
--   2. Each $B$-job has a nondecreasing cost function $f^B_k$, and the **maximum cost of agent $B$** is
--   $$f^B_{\max}(\sigma)=\max_{k=1,\dots,n_B} f^B_k\bigl(C^B_k(\sigma)\bigr),$$
--   defined when $n_B\ge 1$.
--   3. Given a bound $Q$, a schedule is **feasible** for $1\|\sum C^A_i : f^B_{\max}\le Q$ if $f^B_k(C^B_k(\sigma))\le Q$ for every $B$-job $k$; the instance is **feasible** if some feasible schedule exists; a schedule is **optimal** if it is feasible and no feasible schedule has a smaller $\sum C^A_h$.
--   4. A schedule $\sigma$ is **nondominated** if there is no schedule $\bar\sigma$ (of all jobs, with no bound on its cost) with $\sum C^A_h(\bar\sigma)\le\sum C^A_h(\sigma)$, $f^B_{\max}(\bar\sigma)\le f^B_{\max}(\sigma)$, and at least one of the two inequalities strict.
--
--   These are the objects every result of §5.2 of the paper is stated about.
--
--   **Formalization Note** Jobs are `Fin nA ⊕ Fin nB` (`Sum.inl h` is $J^A_{h+1}$, `Sum.inr k` is $J^B_{k+1}$, 0-based). A schedule is a duplicate-free list of all jobs, and completion times are those of the published sequence model `MooreLateJobs.Shared.completionTime`. Processing times and $Q$ are real numbers (the paper's $Q$ is an integer; nothing depends on that). The job type, $f^B_{\max}$ (a `Finset.sup'`, carrying the hypothesis $0<n_B$) and the job-by-job feasibility of item 3 (which needs no nonemptiness) are those of the shared definition `TwoAgentSched.MaxMax.Model` (`Job`, `maxCostB`, `IsFeasible`), which this module imports; it adds $\sum C^A_h$, feasible instances, optimality and nondominance for $(\sum C^A_h, f^B_{\max})$.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), pp. 231–232, §3 (objective functions, nondominated schedules, CP, feasible instance); p. 233, §5

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_TwoAgentSched_MaxMax_Model

namespace TwoAgentSched.TotalMax

/-- The total completion time of agent A, `Σ_h C^A_h(σ)` (§3, p. 231, with `w_i = 1`), of the
sequence `l` with processing times `p`. -/
noncomputable def totalCompletionA {nA nB : ℕ} (p : TwoAgentSched.MaxMax.Job nA nB → ℝ) (l : List (TwoAgentSched.MaxMax.Job nA nB)) : ℝ :=
  ∑ h : Fin nA, MooreLateJobs.Shared.completionTime p l (Sum.inl h)

/-- A feasible instance of `1‖ΣC^A_i : f^B_max ≤ Q` (§3, p. 232): at least one feasible schedule
exists. -/
def IsFeasibleInstance {nA nB : ℕ} (p : TwoAgentSched.MaxMax.Job nA nB → ℝ) (fB : Fin nB → ℝ → ℝ) (Q : ℝ) : Prop :=
  ∃ l : List (TwoAgentSched.MaxMax.Job nA nB), TwoAgentSched.MaxMax.IsFeasible p fB Q l

/-- An optimal schedule of `1‖ΣC^A_i : f^B_max ≤ Q` (CP, §3, p. 232): feasible, and no feasible
schedule has a smaller total completion time of agent A. -/
def IsOptimal {nA nB : ℕ} (p : TwoAgentSched.MaxMax.Job nA nB → ℝ) (fB : Fin nB → ℝ → ℝ) (Q : ℝ)
    (l : List (TwoAgentSched.MaxMax.Job nA nB)) : Prop :=
  TwoAgentSched.MaxMax.IsFeasible p fB Q l ∧
    ∀ l' : List (TwoAgentSched.MaxMax.Job nA nB), TwoAgentSched.MaxMax.IsFeasible p fB Q l' → totalCompletionA p l ≤ totalCompletionA p l'

/-- A nondominated schedule for the objectives `f^A = ΣC^A_i` and `f^B = f^B_max` (§3, p. 231):
`l` is a schedule of all jobs, and there is no schedule `l'` (of all jobs, with no bound on its
B-cost) with `ΣC^A_i(l') ≤ ΣC^A_i(l)`, `f^B_max(l') ≤ f^B_max(l)` and at least one of the two
inequalities strict. -/
def IsNondominated {nA nB : ℕ} (hB : 0 < nB) (p : TwoAgentSched.MaxMax.Job nA nB → ℝ) (fB : Fin nB → ℝ → ℝ)
    (l : List (TwoAgentSched.MaxMax.Job nA nB)) : Prop :=
  MooreLateJobs.Shared.IsSchedule Finset.univ l ∧
    ¬ ∃ l' : List (TwoAgentSched.MaxMax.Job nA nB), MooreLateJobs.Shared.IsSchedule Finset.univ l' ∧
      totalCompletionA p l' ≤ totalCompletionA p l ∧ TwoAgentSched.MaxMax.maxCostB hB p fB l' ≤ TwoAgentSched.MaxMax.maxCostB hB p fB l ∧
      (totalCompletionA p l' < totalCompletionA p l ∨ TwoAgentSched.MaxMax.maxCostB hB p fB l' < TwoAgentSched.MaxMax.maxCostB hB p fB l)

end TwoAgentSched.TotalMax


