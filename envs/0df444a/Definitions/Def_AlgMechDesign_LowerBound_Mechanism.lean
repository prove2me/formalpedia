-- Prove2me | Definitions.Def_AlgMechDesign_LowerBound_Mechanism
-- name    : AlgMechDesign_LowerBound_Mechanism
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T18:36:11.411364+00:00
-- url     : https://prove2.me/theorems/82eda086-4060-4075-bc40-a87a059a82cc
-- title:
--   General mechanisms with arbitrary strategy sets and implementation in dominant strategies
-- statement:
--   This file encodes Nisan and Ronen's general notion of a mechanism (Definition 3) for the task scheduling problem, together with implementation in dominant strategies.
--
--   A **mechanism** $m = (o, p)$ gives each agent $i$ a set $A^i$ of strategies (an arbitrary set, not necessarily the set of types). For a strategy profile $a = (a^1,\dots,a^n)$ it produces an output $o(a)$, which here is an allocation of the $k$ tasks to the $n$ agents, and a payment $p^i(a)$ handed to each agent. Agent $i$ of type $t^i$ has utility
--
--   $$
--   u^i(a) = p^i(a) - t^i\big(o^i(a)\big),
--   $$
--
--   where $o^i(a)$ is the set of tasks allocated to $i$ and $t^i(X)=\sum_{j\in X} t^i_j$.
--
--   1. A strategy $a^i \in A^i$ is **dominant** for agent $i$ of type $t^i$ if for every profile $a^{-i}$ of the other agents (dominant or not) and every $a'^i\in A^i$, $u^i(a^i,a^{-i}) \ge u^i(a'^i, a^{-i})$.
--   2. The mechanism **implements a $c$-approximation** for task scheduling with dominant strategies if (a) every agent of every positive type has a dominant strategy, and (b) for every positive type vector $t$ and every tuple $a$ in which each $a^i$ is dominant for $t^i$, the output satisfies $g(o(a),t) \le c\cdot g(y,t)$ for every allocation $y$.
--
--   Theorem 4.6 is a statement about all such mechanisms, whatever their strategy sets.
--
--   **Formalization Note** Strategy sets are a family of types `A : Fin n → Type*` and profiles are dependent functions `(i : Fin n) → A i`; agent $i$'s deviation is `Function.update a i ai'`. Condition (a) is part of the definition, so a mechanism without dominant strategies does not implement anything vacuously. Condition (b) is the paper's "for each tuple of dominant strategies the output satisfies the specification", with the specification being $c$-approximation of the make-span (Definition 2).
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, pp. 171-172, Definition 3 (A Mechanism), items 1-4; p. 171, Definition 2 (c-approximation)

import Mathlib
import Definitions.Def_AlgMechDesign_LowerBound_Model

namespace AlgMechDesign.LowerBound

open Finset

/-- Utility of agent `i` with true type `ti` in a general mechanism `(o, p)` (Def. 3,
pp. 171–172) when the strategy profile is `b`: agent `i` has strategy set `A i`, the output
`o b` is an allocation of the `k` tasks, and `p b i` is the payment handed to agent `i`. The
utility is `vⁱ(tⁱ, o) + pⁱ` with `vⁱ(tⁱ, o) = -tⁱ(oⁱ)`. -/
def genUtility {n k : ℕ} {A : Fin n → Type*} (o : ((i : Fin n) → A i) → (Fin k → Fin n))
    (p : ((i : Fin n) → A i) → Fin n → ℝ) (b : (i : Fin n) → A i) (i : Fin n)
    (ti : Fin k → ℝ) : ℝ :=
  p b i - taskTime ti (taskSet (o b) i)

/-- The strategy `ai ∈ Aⁱ` is dominant for agent `i` of type `ti` (Def. 3, item 4): for every
strategy profile `a⁻ⁱ` of the other agents (dominant or not) and every alternative strategy
`a'ⁱ`, playing `ai` gives agent `i` at least the utility of playing `a'ⁱ`. -/
def IsDominant {n k : ℕ} {A : Fin n → Type*} (o : ((i : Fin n) → A i) → (Fin k → Fin n))
    (p : ((i : Fin n) → A i) → Fin n → ℝ) (i : Fin n) (ti : Fin k → ℝ) (ai : A i) : Prop :=
  ∀ a : (j : Fin n) → A j, ∀ ai' : A i,
    genUtility o p (Function.update a i ai') i ti ≤ genUtility o p (Function.update a i ai) i ti

/-- The mechanism `(o, p)` implements a `c`-approximation for task scheduling with dominant
strategies (Def. 3, item 4, with the specification of Def. 2): every agent of every positive
type has a dominant strategy, and for every positive type vector `t` and every tuple `a` of
dominant strategies for `t`, the output `o a` has make-span at most `c` times that of every
allocation. -/
def Implements {n k : ℕ} [NeZero n] {A : Fin n → Type*}
    (o : ((i : Fin n) → A i) → (Fin k → Fin n)) (p : ((i : Fin n) → A i) → Fin n → ℝ)
    (c : ℝ) : Prop :=
  (∀ i : Fin n, ∀ ti : Fin k → ℝ, IsAgentType ti → ∃ ai : A i, IsDominant o p i ti ai) ∧
    ∀ t : Fin n → Fin k → ℝ, IsType t → ∀ a : (i : Fin n) → A i,
      (∀ i, IsDominant o p i (t i) (a i)) →
        ∀ y : Fin k → Fin n, makespan t (o a) ≤ c * makespan t y

end AlgMechDesign.LowerBound


