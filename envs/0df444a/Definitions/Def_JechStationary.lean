-- Prove2me | Definitions.Def_JechStationary
-- name    : JechStationary
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-23T02:25:28.597814+00:00
-- url     : https://prove2.me/theorems/1e5ad877-a768-4de9-8648-3b1afc63c813
-- title:
--   Clubs, stationary sets and normal cardinal sequences (Jech, Chapter 8)
-- statement:
--   This bundle fixes the vocabulary of Jech's Chapter 8 ("Stationary Sets", pp. 91-98) for the rest of the mission.
--
--   For a cardinal $\kappa$, write $\mathrm{Below}(\kappa)$ for the set of ordinals $\{\alpha : \alpha < \kappa\}$ with its usual well-ordering; when $\kappa$ is regular and uncountable this is Jech's ambient well-ordered set $\kappa$. A set $C \subseteq \kappa$ is **closed unbounded** (a *club*) when it is unbounded in $\kappa$ and contains all of its limit points below $\kappa$, and $S \subseteq \kappa$ is **stationary** when $S \cap C \neq \emptyset$ for every club $C$ (Jech, Definition 8.1). These two notions are taken from Mathlib, where a club is defined as a cofinal set closed under suprema of directed subsets, and a stationary set as one meeting every club.
--
--   The **diagonal intersection** of a family $\langle X_\alpha : \alpha < \kappa\rangle$ of subsets of $\kappa$ (Jech, equation (8.3)) is
--
--   $$\mathop{\triangle}_{\alpha<\kappa} X_\alpha \;=\; \Bigl\{\xi < \kappa \;:\; \xi \in \bigcap_{\alpha<\xi} X_\alpha\Bigr\}.$$
--
--   An ordinal function $f$ on $S$ is **regressive** when $f(\alpha) < \alpha$ for every $\alpha \in S$ other than the least element (Jech, Definition 8.6).
--
--   A sequence of cardinals $\langle \kappa_\alpha : \alpha < \delta\rangle$ is **normal** when it is strictly increasing and continuous, i.e. $\kappa_\alpha = \sup_{\beta<\alpha}\kappa_\beta$ at every limit stage $\alpha$.
--
--   Finally, the **Singular Cardinal Hypothesis at $\kappa$** (Jech, p. 58) is the implication: if $\kappa$ is singular and $2^{\operatorname{cf}\kappa} < \kappa$, then $\kappa^{\operatorname{cf}\kappa} = \kappa^{+}$.
--
--   These definitions are the shared interface of the whole Jech series: the club filter and the stationary ideal reappear in the chapters on combinatorial set theory, large cardinals, and pcf theory.
--
--   **Formalization Note** The ambient well-order is the Mathlib type `k.ord.ToType` of ordinals below `k`, so that the index set of the diagonal intersection literally *is* the ambient set and no side condition `ξ < κ` has to be carried around. `IsSuccLimit` is Mathlib's notion of a limit element of a well-order, and `Order.succ` on `Cardinal` is the cardinal successor $\kappa^{+}$.
-- source:
--   Thomas Jech, Set Theory, The Third Millennium Edition, revised and expanded, Springer Monographs in Mathematics, Springer 2003, ISBN 3-540-44085-2, Chapter 8, pp. 91-98 (Definitions 8.1, 8.6, equation (8.3)) and Chapter 5, p. 58 (Singular Cardinal Hypothesis)

import Mathlib

namespace JechSetTheory

open Cardinal Order Set

/-- `JechSetTheory.Below k` is the type of ordinals below the cardinal `k`,
with its usual well-ordering.  For a regular uncountable cardinal `k` this is
Jech's `κ` viewed as a well-ordered set, so that Mathlib's `IsClub` and
`IsStationary` (a set is stationary when it meets every club) express Jech's
Definition 8.1. -/
abbrev Below (k : Cardinal) : Type _ := k.ord.ToType

/-- The diagonal intersection of a family `X` of subsets of a well-ordered type,
indexed by the type itself (Jech, equation (8.3)):
`△ X = {x | x ∈ X a for every a < x}`. -/
def diagInter {α : Type*} [LinearOrder α] (X : α → Set α) : Set α :=
  {x | ∀ a < x, x ∈ X a}

/-- `f` is regressive on `S` (Jech, Definition 8.6): `f x < x` for every `x ∈ S`
that is not the least element. -/
def IsRegressiveOn {α : Type*} [Preorder α] (S : Set α) (f : α → α) : Prop :=
  ∀ x ∈ S, ¬ IsMin x → f x < x

/-- A normal sequence of cardinals: strictly increasing, and continuous at every
limit stage (Jech, Chapter 8, hypothesis of Lemma 8.14). -/
def IsNormalCardinalSeq {α : Type*} [LinearOrder α] (f : α → Cardinal) : Prop :=
  StrictMono f ∧ ∀ x : α, IsSuccLimit x → f x = ⨆ y : Set.Iio x, f y

/-- The Singular Cardinal Hypothesis at the cardinal `k` (Jech, Chapter 5,
p. 58): if `k` is singular and `2 ^ cf k < k`, then `k ^ cf k = k⁺`. -/
def SCHAt (k : Cardinal) : Prop :=
  k.IsSingular → 2 ^ k.ord.cof < k → k ^ k.ord.cof = Order.succ k

end JechSetTheory


