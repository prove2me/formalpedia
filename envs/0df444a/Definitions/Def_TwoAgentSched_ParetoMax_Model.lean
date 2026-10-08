-- Prove2me | Definitions.Def_TwoAgentSched_ParetoMax_Model
-- name    : TwoAgentSched_ParetoMax_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T07:37:46.441523+00:00
-- url     : https://prove2.me/theorems/19410b7e-501e-4ea9-90a9-b312124d6ee3
-- title:
--   §3 and §11: two agents on one machine, the maximum costs $f^A_{\max}$, $f^B_{\max}$, nondominated schedules and nondominated pairs
-- statement:
--   Two agents, A and B, share one machine. Agent A owns the jobs $J^A_1,\dots,J^A_{n_A}$ and agent B owns $J^B_1,\dots,J^B_{n_B}$; every job $j$ has a processing time $p_j$, all jobs are available at time $0$, and a **schedule** $\sigma$ is an ordering of all $n_A+n_B$ jobs, processed one after another from time $0$ without idle time. The completion time $C_j(\sigma)$ of a job is the sum of the processing times of the jobs up to and including it.
--
--   Each A-job carries a cost function $f^A_h$ and each B-job a cost function $f^B_k$ of its completion time. This module defines:
--
--   1. the **maximum costs** of the two agents,
--   $$f^A_{\max}(\sigma)=\max_{1\le h\le n_A} f^A_h\big(C^A_h(\sigma)\big),\qquad f^B_{\max}(\sigma)=\max_{1\le k\le n_B} f^B_k\big(C^B_k(\sigma)\big);$$
--   2. **nondominated schedules**: $\sigma$ is nondominated if there is no schedule $\bar\sigma$ with $f^A_{\max}(\bar\sigma)\le f^A_{\max}(\sigma)$ and $f^B_{\max}(\bar\sigma)\le f^B_{\max}(\sigma)$, at least one of the two inequalities strict;
--   3. a nondominated schedule $\sigma$ **corresponds to** the pair $(y^A,y^B)$ if $f^A_{\max}(\sigma)=y^A$ and $f^B_{\max}(\sigma)=y^B$; a **nondominated pair** is a pair to which some nondominated schedule corresponds, and $\mathcal N\subseteq\mathbb R^2$ denotes the set of all nondominated pairs;
--   4. **precedence in a schedule**: job $a$ precedes job $b$ in $\sigma$ if $a$ occurs before $b$.
--
--   These are the objects of §11.1 of the paper, the Pareto version $1\|f^A_{\max}\circ f^B_{\max}$ of the two-agent problem in which both agents measure a schedule by the largest cost of their jobs.
--
--   **Formalization Note** Jobs are the type $\mathrm{Fin}\,n_A\oplus\mathrm{Fin}\,n_B$: `Sum.inl h` is $J^A_{h+1}$ and `Sum.inr k` is $J^B_{k+1}$ (0-based indices). Schedules, completion times and the "no idle time" convention come from the published definition `MooreLateJobs.Shared.completionTime`. $f^A_{\max}$ needs $n_A\ge1$ and $f^B_{\max}$ needs $n_B\ge1$; these are explicit arguments. Precedence compares the first positions of the two jobs in the list; schedules contain every job exactly once. $\mathcal N$ is a set of real pairs, so equivalent schedules (the same pair) are counted once.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 231, §3 (jobs, f_max, nondominated schedule, nondominated pair); p. 239, §11 (one schedule per nondominated pair) and Lemma 11.1 (precedence)

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_TwoAgentSched_MaxMax_Model

namespace TwoAgentSched.ParetoMax

/-- `l` is a nondominated schedule corresponding to the pair `y = (y^A, y^B)` (§3, p. 231, and
§11, p. 239): `l` is nondominated, `f^A_max(l) = y^A` and `f^B_max(l) = y^B`. -/
def IsNondominatedFor {nA nB : ℕ} (hA : 0 < nA) (hB : 0 < nB) (p : TwoAgentSched.MaxMax.Job nA nB → ℝ)
    (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ) (y : ℝ × ℝ) (l : List (TwoAgentSched.MaxMax.Job nA nB)) : Prop :=
  TwoAgentSched.MaxMax.IsNondominated hA hB p fA fB l ∧ TwoAgentSched.MaxMax.maxCostA hA p fA l = y.1 ∧ TwoAgentSched.MaxMax.maxCostB hB p fB l = y.2

/-- A nondominated pair of objective function values (§3, p. 231): the pair
`(f^A_max(σ), f^B_max(σ))` of some nondominated schedule `σ`. -/
def IsNondominatedPair {nA nB : ℕ} (hA : 0 < nA) (hB : 0 < nB) (p : TwoAgentSched.MaxMax.Job nA nB → ℝ)
    (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ) (y : ℝ × ℝ) : Prop :=
  ∃ l : List (TwoAgentSched.MaxMax.Job nA nB), IsNondominatedFor hA hB p fA fB y l

/-- The set of all nondominated pairs `(y^A, y^B)` of `1‖f^A_max ∘ f^B_max` (§11, p. 239: the
pairs `(y^A_1, y^B_1), …, (y^A_k, y^B_k)` that the problem PP asks for). -/
def ndPairs {nA nB : ℕ} (hA : 0 < nA) (hB : 0 < nB) (p : TwoAgentSched.MaxMax.Job nA nB → ℝ)
    (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ) : Set (ℝ × ℝ) :=
  {y | IsNondominatedPair hA hB p fA fB y}

/-- Job `a` precedes job `b` in the sequence `l` (§11.1, p. 239): `a` occurs before `b`, i.e.
its position in `l` is smaller. Used for jobs that both occur in `l` (schedules contain every
job exactly once). -/
def Precedes {nA nB : ℕ} (l : List (TwoAgentSched.MaxMax.Job nA nB)) (a b : TwoAgentSched.MaxMax.Job nA nB) : Prop :=
  l.idxOf a < l.idxOf b

end TwoAgentSched.ParetoMax


