-- Prove2me | Definitions.Def_TwoAgentSched_Knapsack_Model
-- name    : TwoAgentSched_Knapsack_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:38:10.875189+00:00
-- url     : https://prove2.me/theorems/22645e91-3532-4ed4-81a7-75dd024c0cac
-- title:
--   §3, §5.1, §8: two agents on one machine, $\sum w_iC^A_i$, $C^B_{\max}$, $\sum U^B_i$, and the recognition language
-- statement:
--   The two-agent single-machine model of §3 of Agnetis, Mirchandani, Pacciarelli and Pacifici, specialised to the objectives of §5.1 and §8.
--
--   An **instance** has two agents. Agent $A$ owns jobs $J^A_1,\dots,J^A_{n_A}$ with processing times $p^A_h$ and weights $w^A_h$; agent $B$ owns jobs $J^B_1,\dots,J^B_{n_B}$ with processing times $p^B_k$. All data are nonnegative integers, and all jobs are available at time $0$. Since all objectives are regular, a **schedule** $\sigma$ is a sequence of all $n_A+n_B$ jobs processed one after another from time $0$ without idle time; $C_j(\sigma)$ is the completion time of job $j$, i.e. the total processing time of $j$ and all jobs before it.
--
--   The objectives used are
--   1. agent $A$'s total weighted completion time $\sum_{h=1}^{n_A}w^A_hC^A_h(\sigma)$;
--   2. agent $B$'s makespan $C^B_{\max}(\sigma)=\max_kC^B_k(\sigma)$;
--   3. for due dates $d^B_k$, the number $\sum_k U^B_k(\sigma)$ of late $B$-jobs, $J^B_k$ being late iff $C^B_k(\sigma)>d^B_k$.
--
--   For thresholds $Q_A,Q_B$, a sequence $\sigma$ **meets** the recognition problem $1\|\sum w_iC^A_i\le Q_A,\ C^B_{\max}\le Q_B$ (p. 232) if
--
--   $$\sum_{h=1}^{n_A}w^A_hC^A_h(\sigma)\le Q_A\qquad\text{and}\qquad C^B_k(\sigma)\le Q_B\ \text{ for every } k,$$
--
--   and the instance is a **yes-instance** if some sequence meets it. Likewise a sequence meets $1\|\sum w_iC^A_i\le Q_A,\ \sum U^B_i\le Q'$ (§8) if $\sum_h w^A_hC^A_h\le Q_A$ and at most $Q'$ $B$-jobs are late.
--
--   An instance with thresholds $Q_A,Q_B\in\mathbb N$ is coded by the natural numbers $n_A,n_B,p^A_1,\dots,p^A_{n_A},w^A_1,\dots,w^A_{n_A},p^B_1,\dots,p^B_{n_B},Q_A,Q_B$, each in binary; $n_A$ and $n_B$ fix the block lengths, so the code determines the instance. The **target language** is the set of codes of yes-instances, for every $n_A,n_B\ge0$.
--
--   This is the target problem of Theorem 5.2 and the setting of the §8 observation.
--
--   **Formalization Note** Jobs are `Fin nA ⊕ Fin nB`: `Sum.inl h` is $J^A_{h+1}$ and `Sum.inr k` is $J^B_{k+1}$ (0-based). Sequences and completion times are those of the published `MooreLateJobs.Shared.completionTime` (Moore 1968 series), with the integer processing times cast to $\mathbb R$; completion times are compared with real thresholds. The constraint $C^B_{\max}\le Q_B$ is written as $C^B_k\le Q_B$ for all $k$, which needs no nonemptiness of agent $B$'s job set and is vacuous when $n_B=0$.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), pp. 231–232, §3 (objectives; recognition problem); p. 233, §5.1; p. 237, §8

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_ProjSchedTW_Complexity_Encoding

namespace TwoAgentSched.Knapsack

open CookPvsNP ProjSchedTW.Complexity MooreLateJobs.Shared

/-- An instance of the two-agent single-machine problem with objectives `∑ w_i C^A_i` for agent A
and `C^B_max` for agent B (Agnetis, Mirchandani, Pacciarelli & Pacifici 2004, §3, p. 231, and
§5.1, p. 233). Agent A owns the jobs `J^A_1, …, J^A_{n_A}` with processing times `p^A_h` and
weights `w^A_h`; agent B owns the jobs `J^B_1, …, J^B_{n_B}` with processing times `p^B_k`. All
data are nonnegative integers. The jobs are `Fin nA ⊕ Fin nB`: `Sum.inl h` is `J^A_{h+1}` and
`Sum.inr k` is `J^B_{k+1}` (0-based indices). -/
structure Instance where
  /-- The number `n_A` of jobs of agent A. -/
  nA : ℕ
  /-- The number `n_B` of jobs of agent B. -/
  nB : ℕ
  /-- Processing times `p^A_h` of A's jobs. -/
  pA : Fin nA → ℕ
  /-- Weights `w^A_h` of A's jobs. -/
  wA : Fin nA → ℕ
  /-- Processing times `p^B_k` of B's jobs. -/
  pB : Fin nB → ℕ

namespace Instance

variable (I : Instance)

/-- The processing time of each of the `n_A + n_B` jobs, as a real number. -/
def p : Fin I.nA ⊕ Fin I.nB → ℝ :=
  Sum.elim (fun h => (I.pA h : ℝ)) (fun k => (I.pB k : ℝ))

/-- The completion time `C_j(σ)` of job `j` in the sequence `l`: the machine starts at time `0`
and processes the jobs of `l` in order without idle time (§3, p. 231: all objectives are regular,
so each job starts as soon as the previous one is completed). -/
def C (l : List (Fin I.nA ⊕ Fin I.nB)) (j : Fin I.nA ⊕ Fin I.nB) : ℝ :=
  completionTime I.p l j

/-- Agent A's total weighted completion time `∑_{h} w^A_h C^A_h(σ)`. -/
def sumWC (l : List (Fin I.nA ⊕ Fin I.nB)) : ℝ :=
  ∑ h, (I.wA h : ℝ) * I.C l (Sum.inl h)

/-- The sequence `l` is a feasible schedule of all `n_A + n_B` jobs meeting both thresholds of
the recognition problem `1‖∑ w_iC^A_i ≤ Q_A, C^B_max ≤ Q_B` (p. 232): `∑_h w^A_h C^A_h ≤ Q_A` and
`C^B_k ≤ Q_B` for every B-job `k` (equivalently `C^B_max ≤ Q_B`, with no condition when `n_B = 0`). -/
def Meets (QA QB : ℝ) (l : List (Fin I.nA ⊕ Fin I.nB)) : Prop :=
  IsSchedule Finset.univ l ∧ I.sumWC l ≤ QA ∧ ∀ k, I.C l (Sum.inr k) ≤ QB

/-- The instance with thresholds `Q_A`, `Q_B` is a yes-instance of the recognition problem
`1‖∑ w_iC^A_i ≤ Q_A, C^B_max ≤ Q_B` (p. 232): some sequence meets both thresholds. -/
def RecYes (QA QB : ℝ) : Prop :=
  ∃ l, I.Meets QA QB l

open Classical in
/-- The number `∑ U^B_k(σ)` of late B-jobs of the sequence `l` for the due dates `d^B_k`:
job `J^B_k` is late iff `C^B_k > d^B_k` (§3, p. 231). -/
noncomputable def numLateB (dB : Fin I.nB → ℝ) (l : List (Fin I.nA ⊕ Fin I.nB)) : ℕ :=
  (Finset.univ.filter fun k => dB k < I.C l (Sum.inr k)).card

/-- The sequence `l` is a feasible schedule of all jobs meeting both thresholds of the recognition
problem `1‖∑ w_iC^A_i ≤ Q_A, ∑ U^B_i ≤ Q'` (§8, p. 237) for the B due dates `d^B_k`. -/
def MeetsU (QA : ℝ) (dB : Fin I.nB → ℝ) (Q' : ℕ) (l : List (Fin I.nA ⊕ Fin I.nB)) : Prop :=
  IsSchedule Finset.univ l ∧ I.sumWC l ≤ QA ∧ I.numLateB dB l ≤ Q'

/-- The list of numbers coding the instance with thresholds `Q_A`, `Q_B`:
`n_A, n_B, p^A_1, …, p^A_{n_A}, w^A_1, …, w^A_{n_A}, p^B_1, …, p^B_{n_B}, Q_A, Q_B`. The first two
numbers fix the length of each block, so the list determines the instance and the thresholds. -/
def codeList (QA QB : ℕ) : List ℕ :=
  [I.nA, I.nB] ++ List.ofFn I.pA ++ List.ofFn I.wA ++ List.ofFn I.pB ++ [QA, QB]

end Instance

/-- The language of the recognition problem `1‖∑ w_iC^A_i ≤ Q_A, C^B_max ≤ Q_B` (p. 232): binary
codes (`encNats`, every number in binary) of instances with any numbers `n_A`, `n_B` of jobs and
thresholds `Q_A, Q_B ∈ ℕ` such that some sequence of all jobs meets both thresholds. -/
def targetLang : Lang BSym :=
  { x | ∃ (I : Instance) (QA QB : ℕ), I.RecYes QA QB ∧ x = encNats (I.codeList QA QB) }

end TwoAgentSched.Knapsack


