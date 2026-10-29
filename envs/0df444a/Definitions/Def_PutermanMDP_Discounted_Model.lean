-- Prove2me | Definitions.Def_PutermanMDP_Discounted_Model
-- name    : PutermanMDP_Discounted_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:30:41.604273+00:00
-- url     : https://prove2.me/theorems/694b7291-029d-4d48-b41b-ea5f8daa28db
-- title:
--   Countable-state discounted MDPs and randomized history policies
-- statement:
--   The bounded discounted model extends the general stationary MDP defined in `PutermanMDP.Discounted.MDP`. Let $S$ be a nonempty finite or countable state space and $A_s$ a nonempty standard Borel action space at each state. Rewards $r(s,a)$ and transition probabilities $p(j\mid s,a)$ are stationary, measurable in the action, and satisfy $|r(s,a)|\le M$, $p(j\mid s,a)\ge0$, and $\sum_j p(j\mid s,a)=1$. The discount factor satisfies $0\le\lambda<1$.
--
--   A policy chooses a probability distribution on $A_s$ measurably from the complete observed history. Iterated conditional expectations define the expected reward at each decision epoch, and
--   $$v_\lambda^\pi(s)=\sum_{n=0}^{\infty}\lambda^n\mathbb E_s^\pi[r(X_n,A_n)],\qquad v_\lambda^*(s)=\sup_\pi v_\lambda^\pi(s).$$
--   The comparison class includes every admissible randomized history-dependent policy. A policy is $\varepsilon$-optimal if $v_\lambda^*(s)\le v_\lambda^\pi(s)+\varepsilon$ for every state. Deterministic and randomized stationary policies repeat a decision rule forever. The space $V$ consists of bounded real functions and has norm $\|v\|=\sup_s|v(s)|$.
--
--   **Formalization Note** Decisions are indexed from zero. A length-$t$ history is a vector of $t$ state/action pairs, with the current state passed separately. Kernels impose the usual measurability of behavioral decision rules. Each action space is standard Borel, as in §§2.1.2 and 2.3.2; there is no finite-action restriction. Bounded rewards and stochasticity ensure all reward integrals and discounted series converge and the policy supremum is nonempty and bounded.
--
--   Differences from the source:
--   - encoding: nonempty admissible Borel action subsets and full observed histories → dependent standard Borel action types and zero-based histories of previous state/action pairs, with the current state separate; reason: countable disjoint unions identify the two action representations; measurable policies extend to unused histories without changing returns
--   - encoding: Assumptions 6.0.1–6.0.4 and the expected total discounted reward → a bounded discounted extension of MDP, discounted series of recursively integrated stage rewards, and a supremum over behavioral policies; reason: uniform boundedness supplies §2.3.2 integrability and allows interchange of expectation and the absolutely convergent discounted series
--   - encoding: V and its supremum norm → BoundedValue predicate and supNorm on real functions; reason: the norm is used only on bounded functions in all theorem claims
-- source:
--   Puterman, Markov Decision Processes, Wiley, 1994, p. 143 (PDF 159), Assumptions 6.0.1–6.0.4; §§2.1, 2.3.2, 6.1; DOI 10.1002/9780470316887

import Mathlib
import Definitions.Def_PutermanMDP_Discounted_MDP

open MeasureTheory ProbabilityTheory

namespace PutermanMDP.Discounted

/- Imported dependency source, copied verbatim for tool-free blind auditing.
The active declarations are supplied by the imports above.

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

-/

/-- The bounded discounted specialization of the general stationary MDP.
Neither optimality nor convergence is part of the model data. -/
structure Model (S : Type) [Countable S] [Nonempty S] (A : S → Type)
    [∀ s, MeasurableSpace (A s)] [∀ s, StandardBorelSpace (A s)]
    [∀ s, Nonempty (A s)] extends MDP S A where
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  reward_bounded : ∀ s a, |reward s a| ≤ bound
  discount : ℝ
  discount_nonneg : 0 ≤ discount
  discount_lt_one : discount < 1

variable {S : Type} [Countable S] [Nonempty S] {A : S → Type}
    [∀ s, MeasurableSpace (A s)] [∀ s, StandardBorelSpace (A s)]
    [∀ s, Nonempty (A s)]

/-- Expected reward `n` transitions after the supplied history. Iterated
conditional expectation integrates actions and sums the countable next states.
The Model fields and Policy.stochastic imply that every stage is measurable in h
and bounded in absolute value by M.bound: the base stage integrates a bounded
measurable reward, and each successor averages such rewards with probability rows
and a Markov kernel. Thus the integrands are integrable and the state sums are
absolutely summable; these are consequences of the data, not extra assumptions. -/
noncomputable def expectedReward (M : Model S A) (π : Policy A) :
    ℕ → (t : ℕ) → History A t → S → ℝ
  | 0, t, h, s => ∫ a, M.reward s a ∂(π.action t s h)
  | n + 1, t, h, s => ∫ a, (∑' j : S, M.trans s a j *
      expectedReward M π n (t + 1) (Fin.snoc h ⟨s, a⟩) j) ∂(π.action t s h)

/-- The expected total discounted reward, not a Bellman fixed-point definition.
Uniform boundedness and discount < 1 give absolute convergence, with
|value M π s| ≤ M.bound / (1 - M.discount), uniformly over π and s. -/
noncomputable def value (M : Model S A) (π : Policy A) (s : S) : ℝ :=
  ∑' n : ℕ, M.discount ^ n * expectedReward M π n 0 (fun i => Fin.elim0 i) s

/-- Supremum over all admissible randomized history-dependent policies.
This class is nonempty (constant deterministic rules) and its values have the
uniform bound M.bound / (1 - M.discount). No empty/unbounded supremum occurs. -/
noncomputable def optimalValue (M : Model S A) (s : S) : ℝ :=
  ⨆ π : Policy A, value M π s

/-- Epsilon optimality uniformly over initial states and against every
history-dependent randomized policy. -/
def EpsilonOptimal (M : Model S A) (ε : ℝ) (π : Policy A) : Prop :=
  ∀ s, optimalValue M s ≤ value M π s + ε

/-- The vector space V of bounded real functions, as a predicate. -/
def BoundedValue (v : S → ℝ) : Prop := ∃ C : ℝ, ∀ s, |v s| ≤ C

/-- Sup norm, used only for bounded functions. -/
noncomputable def supNorm (v : S → ℝ) : ℝ := ⨆ s, |v s|

end PutermanMDP.Discounted


