-- Prove2me | Definitions.Def_AlgMechDesign_Additive_Price
-- name    : AlgMechDesign_Additive_Price
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T19:06:08.111992+00:00
-- url     : https://prove2.me/theorems/09d553f0-ca50-4bd6-bfb4-9263df989546
-- title:
--   Prices $p^i(X,t^{-i})$ offered to an agent, and additive mechanisms
-- statement:
--   Fix a direct mechanism $m=(x,p)$ for task scheduling, an agent $i$ and the declarations $t^{-i}$ of the other agents. A set $X$ of tasks is **attainable** for agent $i$ against $t^{-i}$ if some positive declaration $t'^i$ makes the mechanism allocate exactly $X$ to agent $i$: $x^i(t'^i,t^{-i}) = X$.
--
--   The **price offered for $X$ to agent $i$** (Definition 12) is
--
--   $$p^i(X,t^{-i}) = \begin{cases} p^i(t'^i,t^{-i}) & \text{if there exists } t'^i \text{ with } x^i(t'^i,t^{-i}) = X,\\ 0 & \text{otherwise.}\end{cases}$$
--
--   For a truthful mechanism the value in the first case does not depend on which $t'^i$ is used (Proposition 4.4), so the price is well defined.
--
--   A mechanism is **additive** (Definition 13) if for every agent $i$, every type vector $t$ and every set $X$ of tasks,
--
--   $$p^i(X,t^{-i}) = \sum_{j\in X} p^i(\{j\},t^{-i}).$$
--
--   The condition is required for every $X$, attainable or not; in particular (empty sum) $p^i(\emptyset,t^{-i}) = 0$. Additive mechanisms are the class for which Theorem 4.10 shows that no truthful mechanism beats the trivial ratio $n$.
--
--   **Formalization Note** In the first case the witness $t'^i$ is picked by `Classical.choose`, and the price is the payment at `Function.update t i t'^i`; it depends on `t` only through $t^{-i}$. Additivity is required for every positive type vector `t` and every `Finset` of tasks, exactly as Definition 13 states it; it is a condition on the prices of Definition 12, not on the payment function directly.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 178, Definition 12; p. 180, Definition 13

import Mathlib
import Definitions.Def_AlgMechDesign_Additive_Model

namespace AlgMechDesign.Additive

open Finset

/-- The set of tasks `X` is attainable for agent `i` against the other agents' declarations
`t⁻ⁱ`: some positive declaration `t'ⁱ` of agent `i` makes the mechanism allocate exactly `X`
to `i`, i.e. `xⁱ(t'ⁱ, t⁻ⁱ) = X`. Only `t⁻ⁱ` matters, since `t i` is overwritten. -/
def IsAttainable {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) (i : Fin n)
    (t : Fin n → Fin k → ℝ) (X : Finset (Fin k)) : Prop :=
  ∃ ti' : Fin k → ℝ, IsAgentType ti' ∧ taskSet (alloc (Function.update t i ti')) i = X

/-- The price offered for `X` to agent `i` (Def. 12, p. 178):
`pⁱ(X, t⁻ⁱ) = pⁱ(t'ⁱ, t⁻ⁱ)` if some positive `t'ⁱ` has `xⁱ(t'ⁱ, t⁻ⁱ) = X`, and `0` otherwise.
The witness `t'ⁱ` is chosen by `Classical.choose`; for a truthful mechanism the value does not
depend on the choice (Proposition 4.4). Only `t⁻ⁱ` matters, since `t i` is overwritten. -/
noncomputable def price {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (i : Fin n) (X : Finset (Fin k))
    (t : Fin n → Fin k → ℝ) : ℝ :=
  open Classical in
  if h : IsAttainable alloc i t X then pay (Function.update t i (Classical.choose h)) i else 0

/-- Additive mechanism (Def. 13, p. 180): for each agent `i`, positive type vector `t` and set
`X` of tasks (attainable or not), `pⁱ(X, t⁻ⁱ) = ∑_{j ∈ X} pⁱ({j}, t⁻ⁱ)`. -/
def IsAdditive {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) : Prop :=
  ∀ i : Fin n, ∀ t : Fin n → Fin k → ℝ, IsType t → ∀ X : Finset (Fin k),
    price alloc pay i X t = ∑ j ∈ X, price alloc pay i {j} t

end AlgMechDesign.Additive


