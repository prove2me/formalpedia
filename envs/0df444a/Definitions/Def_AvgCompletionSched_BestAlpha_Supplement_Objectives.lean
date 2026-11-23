-- Prove2me | Definitions.Def_AvgCompletionSched_BestAlpha_Supplement_Objectives
-- name    : AvgCompletionSched_BestAlpha_Supplement_Objectives
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T06:49:19.447692+00:00
-- url     : https://prove2.me/theorems/8f78c22e-627b-4a07-a8a5-faf5ef0d15b5
-- title:
--   Weighted completion objectives, attained optima, and Best-α
-- statement:
--   Let $I$ consist of $n$ jobs with processing times $p_j>0$ and release dates $r_j\ge0$. A preemptive schedule $P$ and a nonpreemptive schedule $N$ have the feasibility and completion times of the published model. For job weights $w_j$, write
--
--   $$V_P=\sum_j C^P_j,\qquad V_w(N)=\sum_j w_j C^N_j,\qquad A_w(P,a)=\sum_j w_j C^a_j,\quad 0<a\le1.$$
--
--   Preemptive optimality means $V_P\le V_Q$ for every feasible preemptive $Q$. Weighted nonpreemptive optimality means $V_w(N)\le V_w(Q)$ for every feasible nonpreemptive $Q$. A Best-α parameter $a_*$ belongs to $(0,1]$ and satisfies $A_w(P,a_*)\le A_w(P,a)$ for every $a\in(0,1]$. Thus the optimum and the best parameter are attained, rather than represented by a real infimum that might take a default value. The lower-bound theorem supplies their existence and positive denominator; it uses unit positive weights, which are instances of the weighted problem.
--
--   These interfaces keep the preemptive relaxation separate from the true nonpreemptive benchmark. The completion, α-point, α-order, and offline list recursions are imported from the published model without alteration. Finite jobs have only finitely many list orders, so an attained Best-α objective has the same value as its infimum.
-- source:
--   Chekuri, Motwani, Natarajan, Stein, Approximation Techniques for Average Completion Time Scheduling, SIAM J. Comput. 31(1), 2001, DOI 10.1137/S0097539797327180, pp. 146–148, §1; pp. 153, 155–156, §2, Best-α and Theorem 2.9

import Mathlib
import Definitions.Def_AvgCompletionSched_BestAlpha_Model

set_option autoImplicit false

namespace AvgCompletionSched.BestAlpha.Supplement

open MeasureTheory

variable {n : ℕ} {I : Instance n}

/-- The unweighted preemptive objective, with feasibility supplied by the published type. -/
noncomputable def preemptiveCost (P : PreemptiveSchedule I) : ℝ := ∑ j, P.CP j

/-- The weighted objective of an actual feasible nonpreemptive schedule. -/
def weightedCost (w : Fin n → ℝ) (N : NonpreemptiveSchedule I) : ℝ := ∑ j, w j * N.C j

/-- Optimality is against every feasible schedule, never a real infimum with a default. -/
def OptimalPreemptive (P : PreemptiveSchedule I) : Prop :=
  ∀ Q : PreemptiveSchedule I, preemptiveCost P ≤ preemptiveCost Q

/-- An attained nonpreemptive weighted optimum. Existence is a conclusion of the witness
statements, not an assumption about an unrelated numerical optimum. -/
def OptimalNonpreemptive (w : Fin n → ℝ) (N : NonpreemptiveSchedule I) : Prop :=
  ∀ Q : NonpreemptiveSchedule I, weightedCost w N ≤ weightedCost w Q

/-- One shared alpha determines the whole offline alpha-schedule (published tie rule). -/
noncomputable def alphaCost (P : PreemptiveSchedule I) (w : Fin n → ℝ) (a : ℝ) : ℝ :=
  ∑ j, w j * P.Calpha a j

/-- Best-alpha is an attained minimum over ALL alpha in (0,1]. For a finite instance,
there are only finitely many list orders, hence finitely many objective values. -/
def IsBestAlpha (P : PreemptiveSchedule I) (w : Fin n → ℝ) (a : ℝ) : Prop :=
  a ∈ Set.Ioc (0 : ℝ) 1 ∧ ∀ b ∈ Set.Ioc (0 : ℝ) 1, alphaCost P w a ≤ alphaCost P w b

end AvgCompletionSched.BestAlpha.Supplement


