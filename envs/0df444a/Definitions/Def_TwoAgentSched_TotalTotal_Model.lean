-- Prove2me | Definitions.Def_TwoAgentSched_TotalTotal_Model
-- name    : TwoAgentSched_TotalTotal_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:38:32.146985+00:00
-- url     : https://prove2.me/theorems/d5ab26a4-eb2f-4b1d-9060-0830051270f2
-- title:
--   §3, §9: two agents on one machine, $\sum C^A_i$ and $\sum C^B_i$, and the recognition language
-- statement:
--   The two-agent single-machine model of §3 of Agnetis, Mirchandani, Pacciarelli and Pacifici, specialised to the objectives of §9, in which each agent minimises its own total completion time.
--
--   An **instance** has two agents. Agent $A$ owns jobs $J^A_1,\dots,J^A_{n_A}$ with processing times $p^A_h$; agent $B$ owns jobs $J^B_1,\dots,J^B_{n_B}$ with processing times $p^B_k$. All processing times are nonnegative integers, and all jobs are available at time $0$. Since the objectives are regular, a **schedule** $\sigma$ is a sequence of all $n_A+n_B$ jobs processed one after another from time $0$ without idle time; $C_j(\sigma)$ is the completion time of job $j$, the total processing time of $j$ and of all jobs before it. The objectives are
--
--   $$\sum_{h=1}^{n_A}C^A_h(\sigma)\qquad\text{and}\qquad\sum_{k=1}^{n_B}C^B_k(\sigma).$$
--
--   For thresholds $Q_A,Q_B$, a sequence $\sigma$ **meets** the recognition problem $1\|\sum C^A_i\le Q_A,\ \sum C^B_i\le Q_B$ (p. 232) if $\sum_hC^A_h(\sigma)\le Q_A$ and $\sum_kC^B_k(\sigma)\le Q_B$, and the instance is a **yes-instance** if some sequence meets it.
--
--   An instance with thresholds $Q_A,Q_B\in\mathbb N$ is coded by the natural numbers $n_A,n_B,p^A_1,\dots,p^A_{n_A},p^B_1,\dots,p^B_{n_B},Q_A,Q_B$, each in binary; $n_A$ and $n_B$ fix the block lengths, so the code determines the instance. The **target language** is the set of codes of yes-instances, for all $n_A,n_B\ge0$ and all processing times (the two job sets need not be identical).
--
--   This is the target problem of Theorem 9.2 and the setting of Theorem 9.3.
--
--   **Formalization Note** Jobs are `Fin nA ⊕ Fin nB`: `Sum.inl h` is $J^A_{h+1}$ and `Sum.inr k` is $J^B_{k+1}$ (0-based). Sequences and completion times are those of the published `MooreLateJobs.Shared.completionTime` (Moore 1968 series), with the integer processing times cast to $\mathbb R$; the binary alphabet and codes are the published `ProjSchedTW.Complexity.Encoding`.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), pp. 231–232, §3 (objectives; recognition problem); p. 237, §9

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_ProjSchedTW_Complexity_Encoding

namespace TwoAgentSched.TotalTotal

open CookPvsNP ProjSchedTW.Complexity MooreLateJobs.Shared

/-- An instance of the two-agent single-machine problem with objectives `∑ C^A_i` and `∑ C^B_i`
(Agnetis, Mirchandani, Pacciarelli & Pacifici 2004, §3, p. 231, and §9, p. 237). Agent A owns the
jobs `J^A_1, …, J^A_{n_A}` with processing times `p^A_h`; agent B owns the jobs
`J^B_1, …, J^B_{n_B}` with processing times `p^B_k`. All processing times are nonnegative
integers. The jobs are `Fin nA ⊕ Fin nB`: `Sum.inl h` is `J^A_{h+1}` and `Sum.inr k` is
`J^B_{k+1}` (0-based indices). -/
structure Instance where
  /-- The number `n_A` of jobs of agent A. -/
  nA : ℕ
  /-- The number `n_B` of jobs of agent B. -/
  nB : ℕ
  /-- Processing times `p^A_h` of A's jobs. -/
  pA : Fin nA → ℕ
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

/-- Agent A's total completion time `∑_h C^A_h(σ)`. -/
def sumCA (l : List (Fin I.nA ⊕ Fin I.nB)) : ℝ :=
  ∑ h, I.C l (Sum.inl h)

/-- Agent B's total completion time `∑_k C^B_k(σ)`. -/
def sumCB (l : List (Fin I.nA ⊕ Fin I.nB)) : ℝ :=
  ∑ k, I.C l (Sum.inr k)

/-- The sequence `l` is a schedule of all `n_A + n_B` jobs meeting both thresholds of the
recognition problem `1‖∑ C^A_i ≤ Q_A, ∑ C^B_i ≤ Q_B` (p. 232, p. 237). -/
def Meets (QA QB : ℝ) (l : List (Fin I.nA ⊕ Fin I.nB)) : Prop :=
  IsSchedule Finset.univ l ∧ I.sumCA l ≤ QA ∧ I.sumCB l ≤ QB

/-- The instance with thresholds `Q_A`, `Q_B` is a yes-instance of the recognition problem
`1‖∑ C^A_i ≤ Q_A, ∑ C^B_i ≤ Q_B`: some sequence of all jobs meets both thresholds. -/
def RecYes (QA QB : ℝ) : Prop :=
  ∃ l, I.Meets QA QB l

/-- The list of numbers coding the instance with thresholds `Q_A`, `Q_B`:
`n_A, n_B, p^A_1, …, p^A_{n_A}, p^B_1, …, p^B_{n_B}, Q_A, Q_B`. The first two numbers fix the
length of each block, so the list determines the instance and the thresholds. -/
def codeList (QA QB : ℕ) : List ℕ :=
  [I.nA, I.nB] ++ List.ofFn I.pA ++ List.ofFn I.pB ++ [QA, QB]

end Instance

/-- The language of the recognition problem `1‖∑ C^A_i ≤ Q_A, ∑ C^B_i ≤ Q_B` (p. 232): binary
codes (`encNats`, every number in binary) of instances with any numbers `n_A`, `n_B` of jobs and
any processing times, with thresholds `Q_A, Q_B ∈ ℕ`, such that some sequence of all jobs meets
both thresholds. -/
def targetLang : Lang BSym :=
  { x | ∃ (I : Instance) (QA QB : ℕ), I.RecYes QA QB ∧ x = encNats (I.codeList QA QB) }

end TwoAgentSched.TotalTotal


