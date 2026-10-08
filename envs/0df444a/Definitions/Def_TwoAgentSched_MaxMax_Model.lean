-- Prove2me | Definitions.Def_TwoAgentSched_MaxMax_Model
-- name    : TwoAgentSched_MaxMax_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:38:18.944118+00:00
-- url     : https://prove2.me/theorems/0a013a87-746e-48fa-8d89-72e673d9396f
-- title:
--   §3: two agents on one machine, the maximum costs $f^A_{\max}$, $f^B_{\max}$, the problem $1\|f^A_{\max} : f^B_{\max} \le Q$ and nondominated schedules
-- statement:
--   Two agents, A and B, share one machine. Agent A owns the jobs $J^A_1,\dots,J^A_{n_A}$ and agent B owns $J^B_1,\dots,J^B_{n_B}$; every job $j$ has a processing time $p_j$, all jobs are available at time $0$, and a **schedule** $\sigma$ is an ordering of all $n_A+n_B$ jobs, processed one after another from time $0$ without idle time. The completion time $C_j(\sigma)$ of a job is the sum of the processing times of the jobs up to and including it.
--
--   Each job carries a cost function of its completion time, $f^A_h$ for the A-jobs and $f^B_k$ for the B-jobs. This module defines:
--
--   1. the **maximum costs** of the two agents,
--   $$f^A_{\max}(\sigma)=\max_{1\le h\le n_A} f^A_h\big(C^A_h(\sigma)\big),\qquad f^B_{\max}(\sigma)=\max_{1\le k\le n_B} f^B_k\big(C^B_k(\sigma)\big);$$
--   2. the **constrained optimization problem** $1\|f^A_{\max} : f^B_{\max}\le Q$: a schedule is **feasible** if $f^B_k(C^B_k(\sigma))\le Q$ for every B-job, i.e. $f^B_{\max}(\sigma)\le Q$, and **optimal** if it is feasible and no feasible schedule has a smaller $f^A_{\max}$;
--   3. the same problem with the roles of the agents exchanged, $1\|f^B_{\max} : f^A_{\max}\le Q_A$ (feasible: $f^A_h(C^A_h)\le Q_A$ for every A-job; optimal: no feasible schedule has a smaller $f^B_{\max}$);
--   4. **nondominated** schedules: $\sigma$ is nondominated if there is no schedule $\bar\sigma$ with $f^A_{\max}(\bar\sigma)\le f^A_{\max}(\sigma)$ and $f^B_{\max}(\bar\sigma)\le f^B_{\max}(\sigma)$, at least one of the two inequalities strict.
--
--   These are the objects of §4 of the paper, the scenario in which both agents measure a schedule by the largest cost of their jobs.
--
--   **Formalization Note** Jobs are the type $\mathrm{Fin}\,n_A\oplus\mathrm{Fin}\,n_B$: `Sum.inl h` is $J^A_{h+1}$ and `Sum.inr k` is $J^B_{k+1}$ (0-based indices). Schedules, completion times and the "no idle time" convention come from the published definition `MooreLateJobs.Shared.completionTime`. $f^A_{\max}$ needs $n_A\ge1$ and $f^B_{\max}$ needs $n_B\ge1$; these are explicit arguments. The bound $Q$ is real (the paper says "an integer"; nothing in §4 uses integrality). Feasibility is stated job by job, which is equivalent to $f^B_{\max}\le Q$ and needs no B-job to exist; since it does not involve agent A's objective, the same notion is the feasibility of every problem $1\|f^A : f^B_{\max}\le Q$ of the paper (§5 reuses it). Nondominance here is for the two maximum-cost objectives $(f^A_{\max}, f^B_{\max})$.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 231, §3 (jobs, f_max, nondominated schedule); p. 232, §3 (Constrained Optimization Problem); p. 233, §4.1 (the problem with roles exchanged)

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime

namespace TwoAgentSched.MaxMax

/-- The jobs of the two agents (Agnetis–Mirchandani–Pacciarelli–Pacifici 2004, §3, p. 231):
`Sum.inl h` is the A-job `J^A_{h+1}` (`h : Fin nA`) and `Sum.inr k` is the B-job `J^B_{k+1}`
(`k : Fin nB`); indices are 0-based. -/
abbrev Job (nA nB : ℕ) : Type := Fin nA ⊕ Fin nB

/-- The maximum cost of agent A, `f^A_max(σ) = max_h f^A_h(C^A_h(σ))` (§3, p. 231), of the
sequence `l` (jobs processed in the order of `l`, from time `0`, without idle time, processing
times `p`). Needs at least one A-job (`0 < nA`). -/
noncomputable def maxCostA {nA nB : ℕ} (hA : 0 < nA) (p : Job nA nB → ℝ)
    (fA : Fin nA → ℝ → ℝ) (l : List (Job nA nB)) : ℝ :=
  Finset.univ.sup' ⟨⟨0, hA⟩, Finset.mem_univ _⟩
    (fun h => fA h (MooreLateJobs.Shared.completionTime p l (Sum.inl h)))

/-- The maximum cost of agent B, `f^B_max(σ) = max_k f^B_k(C^B_k(σ))` (§3, p. 231). Needs at
least one B-job (`0 < nB`). -/
noncomputable def maxCostB {nA nB : ℕ} (hB : 0 < nB) (p : Job nA nB → ℝ)
    (fB : Fin nB → ℝ → ℝ) (l : List (Job nA nB)) : ℝ :=
  Finset.univ.sup' ⟨⟨0, hB⟩, Finset.mem_univ _⟩
    (fun k => fB k (MooreLateJobs.Shared.completionTime p l (Sum.inr k)))

/-- A feasible schedule of `1‖f^A_max : f^B_max ≤ Q` (CP, §3, p. 232): a sequence of all
`nA + nB` jobs in which every B-job `k` has `f^B_k(C^B_k) ≤ Q`, i.e. `f^B_max ≤ Q`. The condition
does not involve agent A's objective, so it is also the feasibility of every problem
`1‖f^A : f^B_max ≤ Q` of the paper (e.g. `1‖ΣC^A_i : f^B_max ≤ Q`, §5, p. 233). -/
def IsFeasible {nA nB : ℕ} (p : Job nA nB → ℝ) (fB : Fin nB → ℝ → ℝ) (Q : ℝ)
    (l : List (Job nA nB)) : Prop :=
  MooreLateJobs.Shared.IsSchedule Finset.univ l ∧
    ∀ k : Fin nB, fB k (MooreLateJobs.Shared.completionTime p l (Sum.inr k)) ≤ Q

/-- An optimal schedule of `1‖f^A_max : f^B_max ≤ Q` (CP, §3, p. 232): feasible, and no feasible
schedule has a smaller `f^A_max`. -/
def IsOptimal {nA nB : ℕ} (hA : 0 < nA) (p : Job nA nB → ℝ) (fA : Fin nA → ℝ → ℝ)
    (fB : Fin nB → ℝ → ℝ) (Q : ℝ) (l : List (Job nA nB)) : Prop :=
  IsFeasible p fB Q l ∧
    ∀ l' : List (Job nA nB), IsFeasible p fB Q l' → maxCostA hA p fA l ≤ maxCostA hA p fA l'

/-- A feasible schedule of the problem with the roles of the agents exchanged,
`1‖f^B_max : f^A_max ≤ Q_A` (§4.1, p. 233): a sequence of all jobs in which every A-job `h` has
`f^A_h(C^A_h) ≤ Q_A`. -/
def IsFeasibleSwap {nA nB : ℕ} (p : Job nA nB → ℝ) (fA : Fin nA → ℝ → ℝ) (QA : ℝ)
    (l : List (Job nA nB)) : Prop :=
  MooreLateJobs.Shared.IsSchedule Finset.univ l ∧
    ∀ h : Fin nA, fA h (MooreLateJobs.Shared.completionTime p l (Sum.inl h)) ≤ QA

/-- An optimal schedule of `1‖f^B_max : f^A_max ≤ Q_A` (§4.1, p. 233): feasible for it, and no
feasible schedule has a smaller `f^B_max`. -/
def IsOptimalSwap {nA nB : ℕ} (hB : 0 < nB) (p : Job nA nB → ℝ) (fA : Fin nA → ℝ → ℝ)
    (fB : Fin nB → ℝ → ℝ) (QA : ℝ) (l : List (Job nA nB)) : Prop :=
  IsFeasibleSwap p fA QA l ∧
    ∀ l' : List (Job nA nB), IsFeasibleSwap p fA QA l' → maxCostB hB p fB l ≤ maxCostB hB p fB l'

/-- A nondominated schedule for the objectives `f^A_max`, `f^B_max` (§3, p. 231): `l` is a
schedule of all jobs, and there is no schedule `l'` with `f^A_max(l') ≤ f^A_max(l)`,
`f^B_max(l') ≤ f^B_max(l)` and at least one of the two inequalities strict. -/
def IsNondominated {nA nB : ℕ} (hA : 0 < nA) (hB : 0 < nB) (p : Job nA nB → ℝ)
    (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ) (l : List (Job nA nB)) : Prop :=
  MooreLateJobs.Shared.IsSchedule Finset.univ l ∧
    ¬ ∃ l' : List (Job nA nB), MooreLateJobs.Shared.IsSchedule Finset.univ l' ∧
      maxCostA hA p fA l' ≤ maxCostA hA p fA l ∧ maxCostB hB p fB l' ≤ maxCostB hB p fB l ∧
      (maxCostA hA p fA l' < maxCostA hA p fA l ∨ maxCostB hB p fB l' < maxCostB hB p fB l)

end TwoAgentSched.MaxMax


