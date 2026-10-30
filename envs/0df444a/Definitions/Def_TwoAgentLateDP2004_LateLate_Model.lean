-- Prove2me | Definitions.Def_TwoAgentLateDP2004_LateLate_Model
-- name    : TwoAgentLateDP2004_LateLate_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:46:06.66661+00:00
-- url     : https://prove2.me/theorems/6bc62842-6483-49bc-b90c-887ac48f7ae6
-- title:
--   Two-agent real-time schedules, actual late counts and selected early subsets
-- statement:
--   There are $n$ distinct jobs, each belonging to exactly one of agents $A,B$, with real processing times $p_j\ge0$ and real due dates $d_j$. All jobs are available at time zero on one nonpreemptive machine. A full schedule is a permutation, processed without idle time. Its completion times are prefix sums, and its actual late counts are
--   $$U_X(s)=|\{j:\operatorname{owner}(j)=X,\ C_j(s)>d_j\}|\quad(X=A,B).$$
--   For integer $Q$, feasibility means $U_B(s)\le Q$; optimality means feasibility and $U_A(s)\le U_A(t)$ for every feasible full schedule $t$. Early-first EDD structure means a first block of precisely the actually early jobs, ordered by nondecreasing due date, followed by all actually late jobs.
--   For a prefix of $i$ EDD-numbered jobs, an admissible selected subset $E$ meets every selected due date in index order and omits at most $h$ A-jobs and $k$ B-jobs. Its selected completion is $\sum_{j\in E}p_j$, including zero for the empty set. Omission consumes a budget without asserting actual lateness. These predicates provide a common interface for the two milestones and the goal.
--   **Formalization Note** Jobs use `Fin n`; owner `true` means A. Counts are derived from owners. Negative dates and empty owner classes are included; EDD is a separate hypothesis where required.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici (2004), Scheduling Problems with Two Competing Agents, Operations Research 52(2):229–242, https://doi.org/10.1287/opre.1030.0092, §3, pp.231–232 (PDF pp.3–4); §7 partial-schedule definition, p.236 (PDF p.8)

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_MooreLateJobs_NumLate_lateSet

namespace TwoAgentLateDP2004.LateLate

/-- §3, pp.231–232. `true` owns A, `false` owns B. No numeric discretization.
EDD is imposed separately after Lemma 7.1, exactly as on p.236. -/
structure Input (n : ℕ) where
  owner : Fin n → Bool
  p : Fin n → ℝ
  d : Fin n → ℝ
  p_nonneg : ∀ j, 0 ≤ p j

variable {n : ℕ}

noncomputable def ownerCount (I : Input n) (a : Bool) : ℕ :=
  (Finset.univ.filter (fun j => I.owner j = a)).card

noncomputable def lateCount (I : Input n) (a : Bool) (s : List (Fin n)) : ℕ :=
  ((MooreLateJobs.NumLate.lateSet I.p I.d s).filter (fun j => I.owner j = a)).card

def Feasible (I : Input n) (Q : ℤ) (s : List (Fin n)) : Prop :=
  MooreLateJobs.Shared.IsSchedule Finset.univ s ∧ (lateCount I false s : ℤ) ≤ Q

def Optimal (I : Input n) (Q : ℤ) (s : List (Fin n)) : Prop :=
  Feasible I Q s ∧ ∀ t, Feasible I Q t → lateCount I true s ≤ lateCount I true t

/-- The blocks are defined using actual completion times in the full sequence.
Membership in the second block is not an arbitrary designated-late label. -/
def EarlyFirstEDD (I : Input n) (s : List (Fin n)) : Prop :=
  ∃ e l : List (Fin n), s = e ++ l ∧
    (∀ j ∈ e, MooreLateJobs.Shared.completionTime I.p s j ≤ I.d j) ∧
    (∀ j ∈ l, I.d j < MooreLateJobs.Shared.completionTime I.p s j) ∧
    e.Pairwise (fun j k => I.d j ≤ I.d k)

noncomputable def prefixJobs (n i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => j.val < i)

/-- Selected early jobs; omissions consume budgets, without asserting actual lateness.
§7 p.236, contextual reading of “partial schedule”. -/
def Admissible (I : Input n) (i h k : ℕ) (E : Finset (Fin n)) : Prop :=
  E ⊆ prefixJobs n i ∧
  (∀ j ∈ E, ∑ l ∈ E.filter (fun l => l ≤ j), I.p l ≤ I.d j) ∧
  (((prefixJobs n i) \ E).filter (fun j => I.owner j = true)).card ≤ h ∧
  (((prefixJobs n i) \ E).filter (fun j => I.owner j = false)).card ≤ k

noncomputable def selectedCompletion (I : Input n) (E : Finset (Fin n)) : ℝ :=
  ∑ j ∈ E, I.p j

end TwoAgentLateDP2004.LateLate


