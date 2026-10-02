-- Prove2me | Definitions.Def_TheoryOfGames_Acyclic_Solution
-- name    : TheoryOfGames_Acyclic_Solution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T05:41:59.44369+00:00
-- url     : https://prove2.me/theorems/caea34d4-c4bc-47f6-ad05-6eb9481e0234
-- title:
--   Solution in D for a relation 𝒮 (65:1), and the maxima E^m of a set (65.6.1)
-- statement:
--   Let $D$ be an arbitrary set (the book's "domain") and $\mathcal S$ an arbitrary relation between elements of $D$; $x\mathcal S y$ is read "$x$ dominates $y$". Following 65.1.2, a **solution (in $D$ for $\mathcal S$)** is a set $V \subseteq D$ satisfying
--
--   $$\text{(65:1)}\qquad V = \{\, y \in D : x\mathcal S y \text{ holds for no } x \in V \,\}.$$
--
--   In words: the elements of $V$ are precisely those elements $y$ of $D$ which are dominated by no element of $V$. Thus no element of $V$ dominates another element of $V$, and every element of $D$ outside $V$ is dominated by some element of $V$. This abstracts the book's solution concept for games (30:5:c), with imputations replaced by the elements of $D$ and domination by $\mathcal S$; in graph-theoretic language, $V$ is a kernel of the directed graph with an arc $x \to y$ whenever $x\mathcal S y$.
--
--   Following 65.6.1, for $E \subseteq D$ an element $x$ is a **maximum** of $E$ if $x \in E$ and there is no $y \in E$ with $y\mathcal S x$. The set of all maxima of $E$ is denoted $E^m$.
--
--   **Formalization Note** The elements live in a type `α`; `D` and `V` are sets `Set α` and `S : α → α → Prop` with `S x y` meaning $x\mathcal S y$. `IsSolution D S V` is the set equation (65:1) literally, which forces $V \subseteq D$. `maxima E S` is $E^m$.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 588, 65.1.2, (65:1); p. 594, 65.6.1

import Mathlib

namespace TheoryOfGames.Acyclic

/-- 65.1.2, (65:1): given a domain (set) `D` and a relation `S` between elements of `D`
(`S x y` is read "`x` dominates `y`", the book's `x𝒮y`), a *solution (in `D` for `S`)* is a set
`V ⊆ D` such that the elements of `V` are precisely those elements `y` of `D` for which `S x y`
holds for no element `x` of `V`. The equation `V = {y ∈ D | ∀ x ∈ V, ¬ S x y}` forces `V ⊆ D`. -/
def IsSolution {α : Type*} (D : Set α) (S : α → α → Prop) (V : Set α) : Prop :=
  V = {y | y ∈ D ∧ ∀ x ∈ V, ¬ S x y}

/-- 65.6.1: `x` is a *maximum* of `E` if `x` belongs to `E` and no `y` in `E` with `S y x`
exists; `maxima E S` is the set `E^m` of all maxima of `E`. (For `E = D` and `S` a complete or
partial ordering this is the absolute or relative maximum of 65.4.1 and 65.5.1.) -/
def maxima {α : Type*} (E : Set α) (S : α → α → Prop) : Set α :=
  {x | x ∈ E ∧ ∀ y ∈ E, ¬ S y x}

end TheoryOfGames.Acyclic


