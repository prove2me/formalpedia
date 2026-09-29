-- Prove2me | Definitions.Def_AvgCompletionSched_DelayList_Analysis
-- name    : AvgCompletionSched_DelayList_Analysis
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T20:01:05.767952+00:00
-- url     : https://prove2.me/theorems/a2493c2f-66f9-43fa-965a-2bb0215da5ce
-- title:
--   The sets $B_i$, $A_i$, $O_i$, charged idle time, and the paths $P'_i$ with lengths $\kappa'_i$ of the Delay List analysis
-- statement:
--   This file defines the quantities in which the analysis of Delay List (§4.1) is stated. Fix a list $\pi$ and a Delay List run with start times $s^m_j$ and completion times $C^m_j$.
--
--   1. $p(A)=\sum_{k\in A}p_k$ for a set of jobs $A$.
--   2. **Definition 4.3.** $B_i$ is the set of jobs that come before $J_i$ in the list, including $J_i$; $A_i$ is the set of jobs that come after $J_i$ in the list; $O_i\subseteq A_i$ is the set of jobs of $A_i$ that the algorithm schedules before $J_i$.
--   3. For a set of jobs $A$ and a set of times $T$, the idle time charged to jobs of $A$ in $T$ is the idle time (machines $\times$ time) lying in $T$ that the run charges to some job of $A$.
--   4. **Definition 4.4.** A path $P'_i=J_{j_1},J_{j_2},\dots,J_{j_\ell}$ with $J_{j_\ell}=J_i$ is built backwards: $J_{j_k}$ is the predecessor of $J_{j_{k+1}}$ with the largest completion time among all predecessors $J_c$ of $J_{j_{k+1}}$ with $C^m_c\ge r_{j_{k+1}}$ (ties broken arbitrarily), and $J_{j_1}$ is a job with no predecessor $J_c$ satisfying $C^m_c\ge r_{j_1}$. Its length is the sum of the lengths of the intervals $(0,r_{j_1}],(s^m_{j_1},C^m_{j_1}],\dots,(s^m_{j_\ell},C^m_{j_\ell}]$:
--   $$\kappa'_i=r_{j_1}+\sum_{k=1}^{\ell}p_{j_k}.$$
--
--   **Formalization Note** Because ties in Definition 4.4 are broken arbitrarily, a path is a predicate on lists of jobs, and the statements that use $\kappa'_i$ hold for every path satisfying it; $\kappa'_i$ is a function of the path. "Scheduled before" for $O_i$ refers to the order in which the run schedules jobs, which refines the order of start times.
-- source:
--   Chekuri, Motwani, Natarajan, Stein, Approximation Techniques for Average Completion Time Scheduling, SIAM J. Comput. 31(1), 2001, p. 158 ($p(A)$), p. 159 (Definitions 4.3 and 4.4)

import Mathlib
import Definitions.Def_AvgCompletionSched_DelayList_Model
import Definitions.Def_AvgCompletionSched_DelayList_Algorithm

namespace AvgCompletionSched.DelayList

open MeasureTheory

variable {n : ℕ}

/-- `p(A) = ∑_{k ∈ A} p_k`, the total processing time of a set of jobs (p. 158). -/
noncomputable def psum (I : Instance n) (A : Finset (Fin n)) : ℝ := ∑ k ∈ A, I.p k

open Classical in
/-- `B_i` (Definition 4.3, p. 159): the jobs which come before `J_i` in the list `π`, including
`J_i` itself. -/
noncomputable def listB (π : Fin n ≃ Fin n) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun k => π.symm k ≤ π.symm i

open Classical in
/-- `A_i` (Definition 4.3, p. 159): the jobs which come after `J_i` in the list `π`. -/
noncomputable def listA (π : Fin n ≃ Fin n) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun k => π.symm i < π.symm k

namespace DelayListRun

variable {I : Instance n} {m : ℕ} (D : DelayListRun I m)

open Classical in
/-- `O_i` (Definition 4.3, p. 159): the jobs which are scheduled before `J_i` by the algorithm but
come later in the list than `J_i`. -/
noncomputable def outOfOrder (π : Fin n ≃ Fin n) (i : Fin n) : Finset (Fin n) :=
  (listA π i).filter fun k => D.Before k i

/-- Total idle time charged to the jobs of `A` that lies in the time set `T`. -/
noncomputable def chargedToIn (A : Finset (Fin n)) (T : Set ℝ) : ℝ :=
  ∑ k ∈ A, ∫ t in D.chargedSet k ∩ T, D.idle t

/-- One backward step of the path `P′` of Definition 4.4 (p. 159): `a` is a predecessor of `b`
with `C^m_a ≥ r_b`, and has the largest completion time among all predecessors `c` of `b` with
`C^m_c ≥ r_b` (ties broken arbitrarily). -/
def PathStep (a b : Fin n) : Prop :=
  I.prec a b ∧ I.r b ≤ D.C a ∧ ∀ c, I.prec c b → I.r b ≤ D.C c → D.C c ≤ D.C a

/-- The list `j₁ :: l = [J_{j₁}, J_{j₂}, …, J_{j_ℓ}]` is a path `P′_i` of Definition 4.4
(p. 159) for job `i` with respect to the run `D`: it ends at `J_{j_ℓ} = J_i`, each job is the
predecessor chosen by `PathStep` for the next one, and the process terminates at `J_{j₁}`,
which has no predecessor `c` with `C^m_c ≥ r_{j₁}`. -/
def IsPathPrime (i j₁ : Fin n) (l : List (Fin n)) : Prop :=
  (j₁ :: l).getLast (List.cons_ne_nil _ _) = i ∧
  List.IsChain D.PathStep (j₁ :: l) ∧
  ∀ c, I.prec c j₁ → D.C c < I.r j₁

end DelayListRun

/-- `κ′_i` (Definition 4.4, p. 159) for the path `j₁ :: l`: the sum of the lengths of the time
intervals `(0, r_{j₁}]`, `(s^m_{j₁}, C^m_{j₁}]`, …, `(s^m_{j_ℓ}, C^m_{j_ℓ}]`, i.e.
`r_{j₁} + ∑_k p_{j_k}`. -/
noncomputable def kappaPrime (I : Instance n) (j₁ : Fin n) (l : List (Fin n)) : ℝ :=
  I.r j₁ + ((j₁ :: l).map I.p).sum

end AvgCompletionSched.DelayList


