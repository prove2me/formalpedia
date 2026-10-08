-- Prove2me | Definitions.Def_SingleMachinePrec_Biclique_WeightedCompletion
-- name    : SingleMachinePrec_Biclique_WeightedCompletion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T14:46:50.269013+00:00
-- url     : https://prove2.me/theorems/796b0611-b873-463d-bf2b-d3a53b6602df
-- title:
--   The problem 1 | prec | Σ w_j C_j: weighted sum of completion times and optimal schedules (§1)
-- statement:
--   This file sets up the scheduling problem $1\,|\,\mathrm{prec}\,|\,\sum w_jC_j$ of Ambühl, Mastrolilli, Mutsanas and Svensson (§1, p. 653).
--
--   A finite set $J$ of jobs is to be processed on a single machine that processes at most one job at a time. Each job $j$ has a processing time $p_j$ and a weight $w_j$. Precedence constraints are given by a relation $P$ on the jobs: $(i,j)\in P$ with $i\neq j$ means that job $i$ must be completed before job $j$ can be started. A **schedule** is a non-pre-emptive sequence $\sigma$ of all the jobs of $J$, each listed once, processed one after another from time $0$ without idle time; it is **feasible** if it observes the precedence constraints. The completion time $C_j$ of job $j$ is the sum of the processing times of the jobs up to and including $j$ in $\sigma$, and the value of $\sigma$ is
--
--   $$\mathrm{val}(\sigma)=\sum_{j\in J} w_j C_j .$$
--
--   A feasible schedule $\sigma^*$ is **optimal** if $\mathrm{val}(\sigma^*)\le\mathrm{val}(\sigma)$ for every feasible schedule $\sigma$.
--
--   These are the objects in terms of which Lemma 9.1 bounds the optimal value of the bipartite instance $S_G$.
--
--   **Formalization Note** A schedule is a duplicate-free list whose elements are exactly the jobs of $J$; feasibility is the published `LawlerPrec.MinMax.IsFeasible` (for distinct jobs, $(i,j)\in P$ forces $i$ before $j$) and $C_j$ is the published `MooreLateJobs.Shared.completionTime`. Processing times and weights are real numbers; the paper's nonnegativity and integrality are properties of each instance, and the instance $S_G$ used here has times and weights in $\{0,1\}$. Restricting to sequences without idle time does not change the optimal value, since idle time never decreases a completion time.
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 653, §1

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_LawlerPrec_MinMax_IsFeasible

namespace SingleMachinePrec.Biclique

/-- The objective of `1 | prec | Σ w_j C_j` (Ambühl, Mastrolilli, Mutsanas, Svensson 2011, §1,
p. 653): the weighted sum of completion times `val(σ) = Σ_{j ∈ J} w_j C_j` of the sequence `l` of
the job set `J`. The machine processes the jobs of `l` one after another from time `0`, without
idle time or pre-emption, so `C_j` is the sum of the processing times `p` of the jobs of `l` up
to and including `j` (the published `MooreLateJobs.Shared.completionTime`). -/
noncomputable def weightedCompletion {ι : Type*} [DecidableEq ι] (p w : ι → ℝ) (J : Finset ι)
    (l : List ι) : ℝ :=
  ∑ j ∈ J, w j * MooreLateJobs.Shared.completionTime p l j

/-- `l` is an optimal schedule of `1 | prec | Σ w_j C_j` (§1, p. 653): a sequence of `J` that
observes the precedence constraints `prec` (the published `LawlerPrec.MinMax.IsFeasible`: `prec i j`
with `i ≠ j` forces `i` before `j`), whose weighted sum of completion times is at most that of
every such sequence. -/
def IsOptimalSchedule {ι : Type*} [DecidableEq ι] (prec : ι → ι → Prop) (p w : ι → ℝ)
    (J : Finset ι) (l : List ι) : Prop :=
  LawlerPrec.MinMax.IsFeasible prec J l ∧
    ∀ l' : List ι, LawlerPrec.MinMax.IsFeasible prec J l' →
      weightedCompletion p w J l ≤ weightedCompletion p w J l'

end SingleMachinePrec.Biclique


