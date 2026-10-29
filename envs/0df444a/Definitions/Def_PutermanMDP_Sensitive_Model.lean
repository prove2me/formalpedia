-- Prove2me | Definitions.Def_PutermanMDP_Sensitive_Model
-- name    : PutermanMDP_Sensitive_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:32:23.313814+00:00
-- url     : https://prove2.me/theorems/278165cf-954d-4f61-abe5-f484b1ff35c1
-- title:
--   Sensitive optimality criteria and recurrent-class count
-- statement:
--   Consider a finite nonempty state set $S$, finite nonempty admissible action sets $A_s$, signed real rewards $r(s,a)$, and stochastic transition rows $p(t\mid s,a)$. The model and history-dependent randomized policy type are the published Puterman definitions. A deterministic decision rule $d$ selects an action in $A_s$ at each state. Its stationary policy always uses that action. Histories record completed state-action pairs in chronological order, and policies may depend on the entire history.
--
--   Let $R_n^\pi(h,s)$ be the expected one-stage reward after $n$ further transitions, calculated by finite conditional-probability sums. Define
--   $$v_\lambda^\pi(s)=\sum_{n=0}^\infty\lambda^n R_n^\pi(\varnothing,s),\qquad 0\le\lambda<1.$$
--   For an integer $n\ge-1$, $n$-discount optimality means, for every policy $\pi$ and state $s$,
--   $$\liminf_{\lambda\uparrow1}(1-\lambda)^{-n}[v_\lambda^{\pi^*}(s)-v_\lambda^\pi(s)]\ge0.$$
--   Blackwell optimality means that one threshold $0\le\lambda_0<1$ works for all states, all competing policies, and all $\lambda\in[\lambda_0,1)$. Recurrent classes are the nonempty closed irreducible subsets of the finite chain; their number is computed from the transition matrix.
--
--   These definitions separate the asymptotic criterion from eventual discounted dominance.
--
--   **Formalization Note** The liminf condition uses its epsilon/eventual-lower-bound characterization and therefore permits infinite liminf without extended-real subtraction. Policy probabilities outside $A_s$ are ignored, as in the published policy definition. Finite rewards and stochastic rows make the discounted series absolutely convergent on its stated domain.
-- source:
--   Puterman, Markov Decision Processes, Wiley, 1994, p. 494 (PDF 510), Section 10.1.1; model §2.1; Appendix A.1–A.4; https://doi.org/10.1002/9780470316887

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward

namespace PutermanMDP.Sensitive

/-- Use the published Puterman model and history-dependent randomized policy type. -/
abbrev Model (S A : Type) [Fintype S] [Fintype A] :=
  MarkovDecisionProcesses.StationaryMDP S A

variable {S A : Type} [Fintype S] [Fintype A]

abbrev Policy (M : Model S A) := MarkovDecisionProcesses.AvgHRPolicy M

structure DecisionRule (M : Model S A) where
  action : S → A
  admissible : ∀ s, action s ∈ M.admissible s

open Classical in
noncomputable def stationary {M : Model S A} (d : DecisionRule M) : Policy M :=
  MarkovDecisionProcesses.stationaryPolicy M d.action d.admissible

/-- Conditional expected reward n transitions after a chronological observable history.
The decision epoch is the history length; inaccessible history entries never contribute. -/
noncomputable def expectedReward {M : Model S A} (π : Policy M) :
    ℕ → List (S × A) → S → ℝ
  | 0, h, s => ∑ a ∈ M.admissible s, π.q h.length h s a * M.reward s a
  | n + 1, h, s => ∑ a ∈ M.admissible s, π.q h.length h s a *
      ∑ t, M.trans s a t * expectedReward π n (h ++ [(s, a)]) t

/-- For 0 ≤ beta < 1 this series converges absolutely: finite rewards are uniformly bounded. -/
noncomputable def value {M : Model S A} (π : Policy M) (beta : ℝ) (s : S) : ℝ :=
  ∑' n : ℕ, beta ^ n * expectedReward π n [] s

/-- The epsilon characterization of componentwise liminf ≥ 0 in (10.1.1).
It permits an infinite liminf, without totalized extended-real subtraction. -/
def NDiscountOptimal {M : Model S A} (πstar : Policy M) (n : ℤ) : Prop :=
  -1 ≤ n ∧ ∀ (π : Policy M) (s : S) (ε : ℝ), 0 < ε →
    ∃ beta0 : ℝ, 0 ≤ beta0 ∧ beta0 < 1 ∧
      ∀ beta : ℝ, beta0 ≤ beta → beta < 1 →
        -ε ≤ (1 - beta) ^ (-n) * (value πstar beta s - value π beta s)

/-- One policy and one discount threshold, uniform over all policies and states. -/
def BlackwellOptimal {M : Model S A} (πstar : Policy M) : Prop :=
  ∃ beta0 : ℝ, 0 ≤ beta0 ∧ beta0 < 1 ∧
    ∀ (beta : ℝ), beta0 ≤ beta → beta < 1 →
      ∀ (π : Policy M) (s : S), value π beta s ≤ value πstar beta s

def policyMatrix {M : Model S A} (d : DecisionRule M) : Matrix S S ℝ :=
  fun s t => M.trans s (d.action s) t

def rewardVector {M : Model S A} (d : DecisionRule M) : S → ℝ :=
  fun s => M.reward s (d.action s)

/-- A closed irreducible class of a finite Markov chain; zero-step reachability is allowed. -/
def RecurrentClass [DecidableEq S] (P : Matrix S S ℝ) (C : Finset S) : Prop :=
  C.Nonempty ∧
    (∀ s ∈ C, ∀ t, 0 < P s t → t ∈ C) ∧
    ∀ s ∈ C, ∀ t ∈ C, ∃ n : ℕ, 0 < (P ^ n) s t

noncomputable def recurrentCount [DecidableEq S] (P : Matrix S S ℝ) : ℕ :=
  Set.ncard {C : Finset S | RecurrentClass P C}

end PutermanMDP.Sensitive


