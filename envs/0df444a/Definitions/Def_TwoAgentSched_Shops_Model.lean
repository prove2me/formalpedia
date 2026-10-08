-- Prove2me | Definitions.Def_TwoAgentSched_Shops_Model
-- name    : TwoAgentSched_Shops_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:38:40.364975+00:00
-- url     : https://prove2.me/theorems/1fdd1b13-f75f-4f81-b7c5-93417f9c19ee
-- title:
--   §3 and §10: two agents in a two-machine shop, $C^A_{\max}\le Q_A$, $C^B_{\max}\le Q_B$, and the recognition languages
-- statement:
--   The two-agent model of §3 of Agnetis, Mirchandani, Pacciarelli and Pacifici, in the two-machine shops of §10.
--
--   **Instances.** Agent A owns jobs $J^A_1,\dots,J^A_{n_A}$ and agent B owns jobs $J^B_1,\dots,J^B_{n_B}$. Every job has one operation on machine $M_1$ and one on machine $M_2$; $p^X_{ih}$ is the processing time of job $J^X_i$ on machine $M_h$ ($X=A,B$, $h=1,2$). All $n_A+n_B$ jobs are numbered $0,\dots,n_A+n_B-1$, the A-jobs first.
--
--   **Schedules and thresholds.** A schedule gives each job a start time on each machine. For thresholds $Q_A$, $Q_B$, the condition $C^A_{\max}\le Q_A$ says that every operation of every A-job ends by $Q_A$, and $C^B_{\max}\le Q_B$ says the same for the B-jobs and $Q_B$.
--
--   **Recognition problems** (p. 232). The instance is a yes-instance of
--   $$F2\,\|\,C^A_{\max}\le Q_A,\ C^B_{\max}\le Q_B$$
--   if some feasible two-machine **flow shop** schedule (each job first on $M_1$, then on $M_2$; idle time and different job orders on the two machines allowed) meets both thresholds, and a yes-instance of
--   $$O2\,\|\,C^A_{\max}\le Q_A,\ C^B_{\max}\le Q_B$$
--   if some feasible two-machine **open shop** schedule meets both thresholds.
--
--   **Languages.** An instance with natural-number processing times and thresholds $Q_A,Q_B\in\mathbb N$ is coded as the list $n_A, n_B$, the $p^A_{i1}$, the $p^A_{i2}$, the $p^B_{k1}$, the $p^B_{k2}$, $Q_A$, $Q_B$, every number in binary. The **flow shop language** and the **open shop language** are the sets of codes of yes-instances of the two recognition problems. These are the target languages of the NP-hardness reductions of Theorems 10.1 and 10.2.
--
--   **Formalization Note** Jobs are `Fin (n_A + n_B)`: A-job $J^A_{h+1}$ is `Fin.castAdd n_B h` and B-job $J^B_{k+1}$ is `Fin.natAdd n_A k` (0-based). Start times are real numbers, also for natural-number data. The flow shop feasibility is the published `JohnsonFlowShop.TwoStage.IsFeasible`; the open shop feasibility is `TwoAgentSched.Shops.IsOpenFeasible`. $C^X_{\max}\le Q$ is stated operation by operation, so no maximum over a possibly empty job set is taken. The alphabet and the binary code `encNats` are the published `ProjSchedTW.Complexity.Encoding`.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), pp. 231–232, §3 (model, Recognition Problem); p. 238, §10, §10.1 ("Let p^X_ih be the processing time of job J^X_i on machine h"); p. 238, §10.2

import Mathlib
import Definitions.Def_JohnsonFlowShop_TwoStage_IsFeasible
import Definitions.Def_TwoAgentSched_Shops_OpenShop
import Definitions.Def_ProjSchedTW_Complexity_Encoding

namespace TwoAgentSched.Shops

open CookPvsNP ProjSchedTW.Complexity

/-- An instance of a two-agent two-machine shop problem (Agnetis, Mirchandani, Pacciarelli &
Pacifici 2004, §3, p. 231, and §10, p. 238): agent A owns the jobs `J^A_1, …, J^A_{n_A}`, agent B
owns `J^B_1, …, J^B_{n_B}`, and every job has one operation on machine `M_1` and one on `M_2`.
`pA1 h`, `pA2 h` are the processing times `p^A_{h1}`, `p^A_{h2}` of `J^A_{h+1}` on `M_1`, `M_2`,
and `pB1 k`, `pB2 k` those of `J^B_{k+1}` (0-based indices). The data are real numbers. -/
structure Instance where
  /-- The number `n_A` of jobs of agent A. -/
  nA : ℕ
  /-- The number `n_B` of jobs of agent B. -/
  nB : ℕ
  /-- `p^A_{h1}`: processing time of A's jobs on `M_1`. -/
  pA1 : Fin nA → ℝ
  /-- `p^A_{h2}`: processing time of A's jobs on `M_2`. -/
  pA2 : Fin nA → ℝ
  /-- `p^B_{k1}`: processing time of B's jobs on `M_1`. -/
  pB1 : Fin nB → ℝ
  /-- `p^B_{k2}`: processing time of B's jobs on `M_2`. -/
  pB2 : Fin nB → ℝ

namespace Instance

variable (I : Instance)

/-- The `n_A + n_B` jobs are numbered `Fin (n_A + n_B)`: the A-job `J^A_{h+1}` is number `h`. -/
def aJob (h : Fin I.nA) : Fin (I.nA + I.nB) := Fin.castAdd I.nB h

/-- The B-job `J^B_{k+1}` is number `n_A + k`. -/
def bJob (k : Fin I.nB) : Fin (I.nA + I.nB) := Fin.natAdd I.nA k

/-- Processing time of every job on machine `M_1`, in the numbering `Fin (n_A + n_B)`. -/
def p1 (j : Fin (I.nA + I.nB)) : ℝ := Sum.elim I.pA1 I.pB1 (finSumFinEquiv.symm j)

/-- Processing time of every job on machine `M_2`, in the numbering `Fin (n_A + n_B)`. -/
def p2 (j : Fin (I.nA + I.nB)) : ℝ := Sum.elim I.pA2 I.pB2 (finSumFinEquiv.symm j)

/-- `C^A_max ≤ Q_A` for the start times `s₁` (on `M_1`) and `s₂` (on `M_2`): every operation of
every A-job ends by `Q_A`. (No condition when `n_A = 0`.) -/
def MeetsA (s₁ s₂ : Fin (I.nA + I.nB) → ℝ) (QA : ℝ) : Prop :=
  ∀ h : Fin I.nA, s₁ (I.aJob h) + I.pA1 h ≤ QA ∧ s₂ (I.aJob h) + I.pA2 h ≤ QA

/-- `C^B_max ≤ Q_B`: every operation of every B-job ends by `Q_B`. (No condition when
`n_B = 0`.) -/
def MeetsB (s₁ s₂ : Fin (I.nA + I.nB) → ℝ) (QB : ℝ) : Prop :=
  ∀ k : Fin I.nB, s₁ (I.bJob k) + I.pB1 k ≤ QB ∧ s₂ (I.bJob k) + I.pB2 k ≤ QB

/-- The instance is a yes-instance of the recognition problem
`F2‖C^A_max ≤ Q_A, C^B_max ≤ Q_B` (p. 232, §10.1): some feasible two-machine **flow shop**
schedule (every job is processed on `M_1`, then on `M_2`; real start times, idle time and
different job orders on the two machines allowed) meets both thresholds. -/
def FlowYes (QA QB : ℝ) : Prop :=
  ∃ s₁ s₂ : Fin (I.nA + I.nB) → ℝ,
    JohnsonFlowShop.TwoStage.IsFeasible I.p1 I.p2 s₁ s₂ ∧ I.MeetsA s₁ s₂ QA ∧ I.MeetsB s₁ s₂ QB

/-- The instance is a yes-instance of the recognition problem
`O2‖C^A_max ≤ Q_A, C^B_max ≤ Q_B` (p. 232, §10.2): some feasible two-machine **open shop**
schedule meets both thresholds. -/
def OpenYes (QA QB : ℝ) : Prop :=
  ∃ s₁ s₂ : Fin (I.nA + I.nB) → ℝ,
    IsOpenFeasible I.p1 I.p2 s₁ s₂ ∧ I.MeetsA s₁ s₂ QA ∧ I.MeetsB s₁ s₂ QB

end Instance

/-- An instance with natural-number processing times: the data of the recognition languages. -/
structure NatInstance where
  /-- The number `n_A` of jobs of agent A. -/
  nA : ℕ
  /-- The number `n_B` of jobs of agent B. -/
  nB : ℕ
  /-- `p^A_{h1}`. -/
  pA1 : Fin nA → ℕ
  /-- `p^A_{h2}`. -/
  pA2 : Fin nA → ℕ
  /-- `p^B_{k1}`. -/
  pB1 : Fin nB → ℕ
  /-- `p^B_{k2}`. -/
  pB2 : Fin nB → ℕ

namespace NatInstance

variable (I : NatInstance)

/-- The same instance with its data read as real numbers. -/
def toInstance : Instance where
  nA := I.nA
  nB := I.nB
  pA1 := fun h => (I.pA1 h : ℝ)
  pA2 := fun h => (I.pA2 h : ℝ)
  pB1 := fun k => (I.pB1 k : ℝ)
  pB2 := fun k => (I.pB2 k : ℝ)

/-- The list of numbers coding the instance with thresholds `Q_A`, `Q_B`:
`n_A, n_B, p^A_{11}, …, p^A_{n_A 1}, p^A_{12}, …, p^A_{n_A 2}, p^B_{11}, …, p^B_{n_B 1},
p^B_{12}, …, p^B_{n_B 2}, Q_A, Q_B`. The first two numbers fix the length of each block, so the
list determines the instance and the thresholds. -/
def codeList (QA QB : ℕ) : List ℕ :=
  [I.nA, I.nB] ++ List.ofFn I.pA1 ++ List.ofFn I.pA2 ++ List.ofFn I.pB1 ++ List.ofFn I.pB2 ++
    [QA, QB]

end NatInstance

/-- The language of the recognition problem `F2‖C^A_max ≤ Q_A, C^B_max ≤ Q_B` (p. 232): binary
codes (`encNats`) of instances with any numbers of jobs, natural-number processing times and
thresholds `Q_A, Q_B ∈ ℕ`, having a feasible flow shop schedule (real start times) that meets
both thresholds. -/
def flowLang : Lang BSym :=
  { x | ∃ (I : NatInstance) (QA QB : ℕ),
      I.toInstance.FlowYes QA QB ∧ x = encNats (I.codeList QA QB) }

/-- The language of the recognition problem `O2‖C^A_max ≤ Q_A, C^B_max ≤ Q_B` (p. 232): binary
codes of instances with natural-number data having a feasible open shop schedule (real start
times) that meets both thresholds. -/
def openLang : Lang BSym :=
  { x | ∃ (I : NatInstance) (QA QB : ℕ),
      I.toInstance.OpenYes QA QB ∧ x = encNats (I.codeList QA QB) }

end TwoAgentSched.Shops


