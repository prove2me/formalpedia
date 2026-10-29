-- Prove2me | Definitions.Def_PutermanMDP_Discounted_MDP
-- name    : PutermanMDP_Discounted_MDP
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:29:45.662038+00:00
-- url     : https://prove2.me/theorems/fec8d784-cf2e-4a43-89d8-357672b5f05f
-- title:
--   Stationary Markov decision processes and behavioral policies
-- statement:
--   A stationary **Markov decision process** has a nonempty finite or countable state space $S$, nonempty standard Borel action spaces $A_s$, measurable real rewards $r(s,a)$, and action-measurable transition coordinates satisfying
--   $$p(j\mid s,a)\ge 0,\qquad\sum_{j\in S}p(j\mid s,a)=1.$$
--   This general object imposes no reward bound and has no discount parameter.
--
--   A history before epoch $t$ contains the $t$ previous state/action pairs, with the current state supplied separately. A behavioral policy is a measurable probability kernel from that history to admissible actions at the current state. Deterministic and randomized Markov rules choose an action or an action probability measure at each state; their stationary embeddings repeat the rule forever.
--
--   **Formalization Note** Epochs start at zero. Dependent action types encode admissibility exactly. The histories include every observed state and action; policies may randomize and depend on the entire history. The discounted bounded model is a separate extension of this object.
--
--   Differences from the source:
--   - encoding: nonempty admissible Borel action subsets and full observed histories → dependent standard Borel action types and zero-based histories of previous state/action pairs, with the current state separate; reason: countable disjoint unions identify the two action representations; measurable policies extend to unused histories without changing returns
--   - encoding: stationary finite or countable-state data of Chapter 6 → Countable nonempty state type, measurable real rewards and nonnegative transition rows with HasSum 1; reason: retains Assumptions 6.0.1 and 6.0.4 and the probability normalization
--   - generalization: the Borel model in §2.3.2, printed p. 29, requires reward integrability under every admissible action distribution → the primitive MDP requires measurable rewards but does not require their integrability under every action distribution; reason: this data-only object contains every source model; the discounted Model restores integrability by its uniform reward bound before any expectation or theorem is defined
-- source:
--   Puterman, Markov Decision Processes, Wiley, 1994, Sections 2.1–2.3; Chapter 6, p. 143 (PDF 159), Assumptions 6.0.1 and 6.0.4

import Mathlib

open MeasureTheory ProbabilityTheory

namespace PutermanMDP.Discounted

/-- A stationary Markov decision process with a nonempty countable state space
and nonempty standard Borel admissible actions at each state. This general object
contains only rewards and transition probabilities; boundedness and discounting
belong to the separate discounted Model. -/
structure MDP (S : Type) [Countable S] [Nonempty S] (A : S → Type)
    [∀ s, MeasurableSpace (A s)] [∀ s, StandardBorelSpace (A s)]
    [∀ s, Nonempty (A s)] where
  reward : (s : S) → A s → ℝ
  reward_measurable : ∀ s, Measurable (reward s)
  trans : (s : S) → A s → S → ℝ
  trans_nonneg : ∀ s a j, 0 ≤ trans s a j
  trans_sum : ∀ s a, HasSum (trans s a) 1
  trans_measurable : ∀ s j, Measurable (fun a => trans s a j)

variable {S : Type} [Countable S] [Nonempty S] {A : S → Type}
    [∀ s, MeasurableSpace (A s)] [∀ s, StandardBorelSpace (A s)]
    [∀ s, Nonempty (A s)]

/-- A history before decision `t` records `t` past state/action pairs.
The current state is passed separately. Decisions start at zero. Its sigma algebra
is the finite product of the disjoint-union sigma algebra on Sigma A. -/
abbrev History (A : S → Type) (t : ℕ) := Fin t → Sigma A

/-- Behavioral policies: a probability kernel on admissible actions, for every
observable history and current state. Kernel measurability is the usual
admissibility condition for general (possibly uncountable) action spaces. -/
structure Policy (A : S → Type) [∀ s, MeasurableSpace (A s)] where
  action : (t : ℕ) → (s : S) → Kernel (History A t) (A s)
  stochastic : ∀ t s, IsMarkovKernel (action t s)

/-- Deterministic Markov decision rules. -/
abbrev DecisionRule (A : S → Type) := (s : S) → A s

/-- Randomized Markov decision rules. -/
abbrev RandomRule (A : S → Type) [∀ s, MeasurableSpace (A s)] :=
  (s : S) → ProbabilityMeasure (A s)

/-- Repeating a deterministic decision rule forever. -/
noncomputable def stationary (d : DecisionRule A) : Policy A where
  action := fun _ s => Kernel.deterministic (fun _ => d s) measurable_const
  stochastic := by intros; infer_instance

/-- Repeating a randomized decision rule forever. -/
noncomputable def stationaryRandom (d : RandomRule A) : Policy A where
  action := fun t s => Kernel.const (History A t) (d s : Measure (A s))
  stochastic := by intros; infer_instance

end PutermanMDP.Discounted


