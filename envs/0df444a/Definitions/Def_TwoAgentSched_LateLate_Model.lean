-- Prove2me | Definitions.Def_TwoAgentSched_LateLate_Model
-- name    : TwoAgentSched_LateLate_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:38:08.864883+00:00
-- url     : https://prove2.me/theorems/e9d1d6b9-c19e-4f3b-80ae-c37268e832da
-- title:
--   §3 and §7: two agents on one machine with due dates, late jobs, and the problem $1\|\sum U^A_i : \sum U^B_i \le Q$
-- statement:
--   Two competing agents $A$ and $B$ share one machine. Together they own $n = n_A + n_B$ nonpreemptive jobs $J_1, \dots, J_n$, all released at time $0$. Job $J_j$ has a processing time $p_j \in \mathbb N$, a due date $d_j \in \mathbb N$, and an owner, agent $A$ or agent $B$. Because the objectives are regular, a schedule is a **sequence** $\sigma$ of all $n$ jobs processed one after another from time $0$ without idle time, so the completion time of the job in position $m$ is the sum of the processing times of the first $m$ jobs. Job $J_j$ is **late** in $\sigma$ if $C_j(\sigma) > d_j$ and **early** otherwise. For an agent $X \in \{A, B\}$,
--   $$\sum U^X_i(\sigma) = \#\{\, j : J_j \text{ belongs to } X,\ C_j(\sigma) > d_j \,\}$$
--   is the number of late jobs of $X$. Given an integer $Q \ge 0$, a sequence is **feasible** for the problem $1\|\sum U^A_i : \sum U^B_i \le Q$ if at most $Q$ jobs of $B$ are late, and it is **optimal** if it is feasible and no feasible sequence has fewer late jobs of $A$. The set $\{J_1, \dots, J_i\}$ of the first $i$ jobs is also named here, for the dynamic program of §7.
--
--   These objects are the model of the whole mission: every statement compares the dynamic program with this problem.
--
--   **Formalization Note** Jobs are indexed by `Fin n`, 0-based: the index `j` is the job $J_{j+1}$, so $\{J_1,\dots,J_i\}$ is the set of indices below $i$. One job list with an owner label `ag : Fin n → Agent` follows the paper's own presentation in §7 (jobs of both agents numbered together in EDD order). Processing times and due dates are natural numbers, cast to $\mathbb R$ for the published sequence model `MooreLateJobs.Shared.completionTime` and the published late-job set `MooreLateJobs.NumLate.lateSet` (late iff $d_j < C_j$), which are reused. The constraint is "at most $Q$ late $B$-jobs" ($\le Q$).
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), pp. 231–232, §3 (model, ΣU_i, problem CP); p. 236, §7

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_MooreLateJobs_NumLate_lateSet

namespace TwoAgentSched.LateLate

/-- The two competing agents `A` and `B` (Agnetis et al. 2004, §3, p. 231). -/
inductive Agent
  | A
  | B
  deriving DecidableEq, Repr

/-- The job set `{J_1, …, J_i}` (§7, p. 236). The `n = n_A + n_B` jobs of both agents are indexed
by `Fin n` in EDD order, 0-based: the index `j` stands for the job `J_{j+1}`. So `{J_1, …, J_i}`
is the set of indices `j` with `j < i`. -/
def prefixJobs (n i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun j : Fin n => j.val < i)

/-- The number of late jobs of agent `X` in the sequence `l` (§3, p. 231: `U_j = 1` iff job `J_j`
is late, i.e. its completion time exceeds its due date, `C_j > d_j`). The jobs have processing
times `p` and due dates `d` (natural numbers), and `ag j` is the agent owning job `j`. The
sequence is processed on one machine from time `0` without idle time
(`MooreLateJobs.Shared.completionTime`), and the late jobs are those of
`MooreLateJobs.NumLate.lateSet`. -/
noncomputable def numLate {n : ℕ} (p d : Fin n → ℕ) (ag : Fin n → Agent) (X : Agent)
    (l : List (Fin n)) : ℕ :=
  ((MooreLateJobs.NumLate.lateSet (fun j => (p j : ℝ)) (fun j => (d j : ℝ)) l).filter
    (fun j => ag j = X)).card

/-- A feasible solution of `1‖ΣU^A_i : ΣU^B_i ≤ Q` (§3, p. 232, problem CP; §7, p. 236): a
sequence of all `n` jobs in which at most `Q` jobs of agent `B` are late. -/
def IsFeasible {n : ℕ} (p d : Fin n → ℕ) (ag : Fin n → Agent) (Q : ℕ) (l : List (Fin n)) :
    Prop :=
  MooreLateJobs.Shared.IsSchedule Finset.univ l ∧ numLate p d ag .B l ≤ Q

/-- An optimal schedule of `1‖ΣU^A_i : ΣU^B_i ≤ Q`: a feasible sequence whose number of late
`A`-jobs is minimum among all feasible sequences (§3, p. 232, problem CP). -/
def IsOptimal {n : ℕ} (p d : Fin n → ℕ) (ag : Fin n → Agent) (Q : ℕ) (l : List (Fin n)) :
    Prop :=
  IsFeasible p d ag Q l ∧
    ∀ l' : List (Fin n), IsFeasible p d ag Q l' → numLate p d ag .A l ≤ numLate p d ag .A l'

end TwoAgentSched.LateLate


