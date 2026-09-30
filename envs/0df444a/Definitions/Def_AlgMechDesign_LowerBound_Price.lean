-- Prove2me | Definitions.Def_AlgMechDesign_LowerBound_Price
-- name    : AlgMechDesign_LowerBound_Price
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T18:38:54.865802+00:00
-- url     : https://prove2.me/theorems/de654521-265a-4b28-887c-5f428af2e1fc
-- title:
--   Attainable task sets, the price $p^i(X, t^{-i})$ and price differences $\Delta^i(A,B)$
-- statement:
--   This file defines the price function of Nisan and Ronen (Definition 12) for a direct mechanism $(x,p)$ for task scheduling.
--
--   Fix an agent $i$ and the declarations $t^{-i}$ of the other agents. A set $X$ of tasks is **attainable** for $i$ if some positive declaration $t'^i$ of agent $i$ yields $x^i(t'^i, t^{-i}) = X$. The **price offered for $X$** is
--
--   $$
--   p^i(X, t^{-i}) = \begin{cases} p^i(t'^i, t^{-i}) & \text{if there is a positive } t'^i \text{ with } x^i(t'^i,t^{-i}) = X,\\ 0 & \text{otherwise.}\end{cases}
--   $$
--
--   For disjoint sets $A$ and $B$ of tasks the **price difference** is $\Delta^i(A,B) = p^i(A\cup B, t^{-i}) - p^i(A, t^{-i})$.
--
--   For truthful mechanisms the payment does not depend on which witness $t'^i$ is used (Proposition 4.4), so the price is well defined; these prices are the language in which Proposition 4.5 and Lemma 4.7 are stated.
--
--   **Formalization Note** When several declarations $t'^i$ attain $X$, the witness is picked by `Classical.choose`; nothing is claimed about the choice for non-truthful mechanisms. The price depends only on $t^{-i}$: agent $i$'s own entry of the argument $t$ is overwritten. Unattainable sets have price $0$ exactly as in Definition 12. `priceDiff` is defined for all pairs of sets; the paper uses it only for disjoint ones.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 178, Definition 12 and the Notation before Lemma 4.7 (price difference)

import Mathlib
import Definitions.Def_AlgMechDesign_LowerBound_Model

namespace AlgMechDesign.LowerBound

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

/-- The price difference `Δⁱ(A, B) = pⁱ(A ∪ B, t⁻ⁱ) - pⁱ(A, t⁻ⁱ)` (Notation, p. 178), used for
disjoint sets of tasks `A` and `B`. -/
noncomputable def priceDiff {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (i : Fin n) (t : Fin n → Fin k → ℝ)
    (A B : Finset (Fin k)) : ℝ :=
  price alloc pay i (A ∪ B) t - price alloc pay i A t

end AlgMechDesign.LowerBound


