-- Prove2me | Definitions.Def_PutermanMDP_Multichain_Iteration
-- name    : PutermanMDP_Multichain_Iteration
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T03:00:25.870001+00:00
-- url     : https://prove2.me/theorems/47050994-8aa3-4cc9-8e2b-891016a03b6e
-- title:
--   Printed multichain policy iteration and a separately restricted variant
-- statement:
--   For an admissible stationary rule $d$, evaluation chooses vectors $g,h$ satisfying
--   $$(P_d-I)g=0,\qquad r_d-g+(P_d-I)h=0,$$
--   with $h=h^d$, the canonical bias. Start with any rule. First maximize $P_a g(s)$ over $a\in A_s$, retaining the incumbent action at every state where it already attains this maximum. If any action changes, evaluate the new rule. Otherwise maximize $r(s,a)+P_a h(s)$ over all $A_s$, again retaining each incumbent on ties. Stop if the resulting rule equals the current rule. This is the algorithm printed in (9.2.3)–(9.2.4) and (9.2.7)–(9.2.8).
--
--   A second, separately named run predicate restricts only phase two to $B_s=\{a\in A_s:P_ag(s)=g(s)\}$, including tie retention within this set. It supports the corrected variant; it does not redefine the printed algorithm.
--
--   The predicates specify every evaluation and selection step, leaving choices among nonincumbent maximizers arbitrary. They do not assume termination or optimality.
--
--   **Formalization Note** Iterations start at zero. A terminating finite run is extended by repeating its last rule, so termination is the existence of an index $N$ with $d_{N+1}=d_N$. The source's phase-two set is literally $D$ (componentwise $A_s$); the distinct restricted predicate records the change to $E$ explicitly.
-- source:
--   Puterman, Markov Decision Processes: Discrete Stochastic Dynamic Programming, Wiley, 1994, https://doi.org/10.1002/9780470316887, pp. 452–453 (PDF 468–469), §9.2.1, (9.2.1)–(9.2.8); p. 457 (PDF 473), Theorem 9.2.3

import Mathlib
import Definitions.Def_PutermanMDP_Multichain_Criteria

open MarkovDecisionProcesses

namespace PutermanMDP.Multichain

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq A]

/-- Evaluation equations (9.2.1)–(9.2.2); no optimality is assumed. -/
def Evaluation (M : StationaryMDP S A) (d : Rule M) (g h : S → ℝ) : Prop :=
  (∀ s, act M g s (d.val s) = g s) ∧
  (∀ s, M.reward s (d.val s) - g s + act M h s (d.val s) - h s = 0)

/-- First-phase statewise maximizing rule. -/
def GainMax (M : StationaryMDP S A) (g : S → ℝ) (d : Rule M) : Prop :=
  ∀ s, ∀ a ∈ M.admissible s, act M g s a ≤ act M g s (d.val s)

/-- Incumbent actions are retained wherever already gain-maximizing. -/
def GainTies (M : StationaryMDP S A) (g : S → ℝ) (d e : Rule M) : Prop :=
  ∀ s, (∀ a ∈ M.admissible s, act M g s a ≤ act M g s (d.val s)) → e.val s = d.val s

/-- Incumbent actions are retained wherever already bias-maximizing over all actions. -/
def BiasTies (M : StationaryMDP S A) (h : S → ℝ) (d e : Rule M) : Prop :=
  ∀ s, (∀ a ∈ M.admissible s,
    M.reward s a + act M h s a ≤ M.reward s (d.val s) + act M h s (d.val s)) →
      e.val s = d.val s

/-- The printed two-phase rule, (9.2.3)–(9.2.4), component form (9.2.7)–(9.2.8).
Phase two maximizes over ALL A_s as printed, not just the gain-preserving actions. -/
def PrintedStep (M : StationaryMDP S A) (g h : S → ℝ) (d e : Rule M) : Prop :=
  (¬ GainMax M g d ∧ GainMax M g e ∧ GainTies M g d e) ∨
  (GainMax M g d ∧ FullSelector M h e ∧ BiasTies M h d e)

/-- A run, extended by repeating the last rule if the stopping test succeeds.
The first rule is arbitrary. Equality of two successive rules is the stopping test.
The canonical-bias hypothesis is explicit and evaluation is not an optimality assumption. -/
def PrintedRun (M : StationaryMDP S A) (d : ℕ → Rule M) (g h : ℕ → S → ℝ) : Prop :=
  ∀ n, Evaluation M (d n) (g n) (h n) ∧ h n = bias M (d n) ∧
    PrintedStep M (g n) (h n) (d n) (d (n + 1))

/-- Corrected second phase: maximize over gain-preserving actions and retain ties there.
This is a separate variant, not a reinterpretation of the printed algorithm. -/
def RestrictedStep (M : StationaryMDP S A) (g h : S → ℝ) (d e : Rule M) : Prop :=
  (¬ GainMax M g d ∧ GainMax M g e ∧ GainTies M g d e) ∨
  (GainMax M g d ∧ InE M g e ∧
    (∀ s, ∀ a ∈ M.admissible s, act M g s a = g s →
      M.reward s a + act M h s a ≤ M.reward s (e.val s) + act M h s (e.val s)) ∧
    (∀ s, (∀ a ∈ M.admissible s, act M g s a = g s →
      M.reward s a + act M h s a ≤ M.reward s (d.val s) + act M h s (d.val s)) →
        e.val s = d.val s))

/-- Runs of the separately corrected algorithm, with the same canonical evaluation. -/
def RestrictedRun (M : StationaryMDP S A) (d : ℕ → Rule M) (g h : ℕ → S → ℝ) : Prop :=
  ∀ n, Evaluation M (d n) (g n) (h n) ∧ h n = bias M (d n) ∧
    RestrictedStep M (g n) (h n) (d n) (d (n + 1))

end PutermanMDP.Multichain


