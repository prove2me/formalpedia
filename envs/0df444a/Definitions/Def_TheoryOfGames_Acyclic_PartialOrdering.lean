-- Prove2me | Definitions.Def_TheoryOfGames_Acyclic_PartialOrdering
-- name    : TheoryOfGames_Acyclic_PartialOrdering
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T05:46:28.523786+00:00
-- url     : https://prove2.me/theorems/a7b73f9b-63a2-4645-9ff3-18a14f3b27c6
-- title:
--   Partial ordering (65:B) and the condition (65:G)
-- statement:
--   Let $D$ be a set and $\mathcal S$ a relation on $D$. Following 65.3.2, $\mathcal S$ is a **partial ordering** of $D$ if
--
--   1. (65:B:a) for any two $x, y$ of $D$ at most one of the three relations $x = y$, $x\mathcal S y$, $y\mathcal S x$ holds;
--   2. (65:B:b) $x\mathcal S y$ and $y\mathcal S z$ together imply $x\mathcal S z$ (for $x, y, z$ in $D$).
--
--   For a partial ordering, a maximum of $D$ (an $x \in D$ with no $y \in D$ such that $y\mathcal S x$) is called a relative maximum (65.5.1). The book's **condition (65:G)** reads:
--
--   $$\text{if } y \in D \text{ is not a maximum, then a maximum } x \text{ with } x\mathcal S y \text{ exists.}$$
--
--   Condition (65:G) turns out to be exactly what a partial ordering needs for a solution to exist (65:H).
--
--   **Formalization Note** (65:B:a) is written as three negated conjunctions, one for each pair of the three relations. `ConditionG D S` uses `maxima D S` from the definition item `Solution`.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 590, 65.3.2, (65:B:a), (65:B:b); p. 593, (65:G)

import Mathlib
import Definitions.Def_TheoryOfGames_Acyclic_Solution

namespace TheoryOfGames.Acyclic

/-- 65.3.2: `S` is a *partial ordering* of `D` if
(65:B:a) for any two `x, y` of `D` at most one of the three relations `x = y`, `x S y`, `y S x`
holds, and
(65:B:b) `x S y`, `y S z` together imply `x S z` (for `x, y, z` of `D`). -/
def IsPartialOrdering {α : Type*} (D : Set α) (S : α → α → Prop) : Prop :=
  (∀ x ∈ D, ∀ y ∈ D, ¬ (x = y ∧ S x y) ∧ ¬ (x = y ∧ S y x) ∧ ¬ (S x y ∧ S y x)) ∧
  (∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, S x y → S y z → S x z)

/-- (65:G): if `y` in `D` is not a maximum (of `D`), then a maximum `x` with `x S y` exists. -/
def ConditionG {α : Type*} (D : Set α) (S : α → α → Prop) : Prop :=
  ∀ y ∈ D, y ∉ maxima D S → ∃ x ∈ maxima D S, S x y

end TheoryOfGames.Acyclic


