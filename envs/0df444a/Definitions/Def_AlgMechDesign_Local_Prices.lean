-- Prove2me | Definitions.Def_AlgMechDesign_Local_Prices
-- name    : AlgMechDesign_Local_Prices
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T19:36:10.271718+00:00
-- url     : https://prove2.me/theorems/b06347f6-e26b-41b3-a84e-f7d5c4372eb9
-- title:
--   Prices offered to an agent, local mechanisms, and unique utility maximizers
-- statement:
--   Fix a direct mechanism $(x, p)$ for task scheduling. For a declared type vector $t$ and an agent $i$ write $t^{-i}$ for the declarations of the other agents, $x^i(t)$ for the set of tasks given to $i$, and, for a set $X$ of tasks, $t^i(X) = \sum_{j \in X} t^i_j$ (Notation, p. 178).
--
--   1. A set $X$ is **attainable** for agent $i$ against $t^{-i}$ if some positive declaration $t'^i$ gives $x^i(t'^i, t^{-i}) = X$.
--   2. The **price offered for $X$ to agent $i$** (Definition 12) is
--   $$
--   p^i(X, t^{-i}) = \begin{cases} p^i(t'^i, t^{-i}) & \text{if there exists } t'^i \text{ with } x^i(t'^i, t^{-i}) = X,\\ 0 & \text{otherwise.}\end{cases}
--   $$
--   3. The mechanism is **local** (Definition 14) if for each agent $i$, type vector $t$ and set $X$ of tasks, the price $p^i(X, t^{-i})$ depends only on the other agents' values $\{t^l_j : l \ne i,\ j \in X\}$ on the tasks of $X$: two positive type vectors that agree on these values give the same price.
--   4. Agent $i$'s **utility for the set $X$** at $t$ is $p^i(X, t^{-i}) - t^i(X)$, and $x^i(t)$ is the **unique maximizer** of $i$'s utility at $t$ if every other attainable set $X \neq x^i(t)$ has strictly smaller utility.
--   5. For a set $X$ of tasks and a number $\alpha$, $t(X \xrightarrow{i} \alpha)$ is the type vector obtained from $t$ by setting agent $i$'s time on every task of $X$ to $\alpha$ (Notation, p. 179).
--
--   Locality is a property of the whole price function of Definition 12, including the value $0$ it assigns to sets agent $i$ cannot obtain. The mechanism MinWork of §4.2 is local: its price for $X$ is $\sum_{j \in X} \min_{l \ne i} t^l_j$.
--
--   **Formalization Note** When several declarations give agent $i$ the set $X$, the price uses one of them, chosen by `Classical.choose`; for a truthful mechanism all of them give the same payment (Proposition 4.4), so the value does not depend on the choice. Declarations are positive, as everywhere in the model. Uniqueness of the maximizer is stated over the attainable sets, the family over which Proposition 4.5 holds for every truthful mechanism.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 178, Definition 12 and Notation; p. 179, Notation (t(X →ⁱ α)); p. 180, Definition 14

import Mathlib
import Definitions.Def_AlgMechDesign_Local_Model

namespace AlgMechDesign.Local

open Finset

/-- The set of tasks `xⁱ(t)` that the allocation rule `alloc` gives agent `i` at the declared
type vector `t`. -/
def agentSet {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (t : Fin n → Fin k → ℝ) (i : Fin n) : Finset (Fin k) :=
  univ.filter (fun j => alloc t j = i)

/-- The time `tⁱ(X) = ∑_{j ∈ X} tⁱ_j` agent `i` of type `ti` needs to perform the tasks of `X`
(Notation, p. 178). -/
def setTime {k : ℕ} (ti : Fin k → ℝ) (X : Finset (Fin k)) : ℝ :=
  ∑ j ∈ X, ti j

/-- The set `X` is attainable for agent `i` against `t⁻ⁱ`: some positive declaration `t'ⁱ` of
agent `i` gets exactly `X`, i.e. `xⁱ(t'ⁱ, t⁻ⁱ) = X`. Only `t⁻ⁱ` matters, since `t i` is
overwritten. -/
def IsAttainable {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) (i : Fin n)
    (X : Finset (Fin k)) (t : Fin n → Fin k → ℝ) : Prop :=
  ∃ ti' : Fin k → ℝ, IsAgentType ti' ∧ agentSet alloc (Function.update t i ti') i = X

/-- The price offered for `X` to agent `i` (Def. 12, p. 178):
`pⁱ(X, t⁻ⁱ) = pⁱ(t'ⁱ, t⁻ⁱ)` if some positive `t'ⁱ` has `xⁱ(t'ⁱ, t⁻ⁱ) = X`, and `0` otherwise.
The witness is chosen; for a truthful mechanism the value does not depend on the choice
(Proposition 4.4). -/
noncomputable def price {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (i : Fin n) (X : Finset (Fin k))
    (t : Fin n → Fin k → ℝ) : ℝ :=
  open Classical in
  if h : IsAttainable alloc i X t then pay (Function.update t i (Classical.choose h)) i else 0

/-- A mechanism is local (Def. 14, p. 180) if for each agent `i`, type vector `t` and set `X` of
tasks the price `pⁱ(X, t⁻ⁱ)` depends only on the other agents' values `{tˡ_j | l ≠ i, j ∈ X}`
on the tasks of `X`: two positive type vectors agreeing on those values give the same price. -/
def IsLocal {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) : Prop :=
  ∀ (i : Fin n) (X : Finset (Fin k)) (t t' : Fin n → Fin k → ℝ), IsType t → IsType t' →
    (∀ l, l ≠ i → ∀ j ∈ X, t l j = t' l j) → price alloc pay i X t = price alloc pay i X t'

/-- Agent `i`'s utility for the set `X` at the type vector `t`: `pⁱ(X, t⁻ⁱ) − tⁱ(X)`. -/
noncomputable def setUtility {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (i : Fin n) (X : Finset (Fin k))
    (t : Fin n → Fin k → ℝ) : ℝ :=
  price alloc pay i X t - setTime (t i) X

/-- At `t`, the set `xⁱ(t)` is the unique maximizer of agent `i`'s utility `pⁱ(X, t⁻ⁱ) − tⁱ(X)`
among the attainable sets: every other attainable set gives strictly less. -/
def IsUniqueMaximizer {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (t : Fin n → Fin k → ℝ) (i : Fin n) : Prop :=
  ∀ X : Finset (Fin k), IsAttainable alloc i X t → X ≠ agentSet alloc t i →
    setUtility alloc pay i X t < setUtility alloc pay i (agentSet alloc t i) t

/-- The type `t̂ = t(X →ⁱ α)` (Notation, p. 179): agent `i`'s time on each task of `X` becomes `α`;
every other entry of `t` is unchanged. -/
def setTimes {n k : ℕ} (t : Fin n → Fin k → ℝ) (i : Fin n) (X : Finset (Fin k)) (α : ℝ) :
    Fin n → Fin k → ℝ :=
  Function.update t i (fun j => if j ∈ X then α else t i j)

end AlgMechDesign.Local


