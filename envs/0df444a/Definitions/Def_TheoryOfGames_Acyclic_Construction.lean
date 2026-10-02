-- Prove2me | Definitions.Def_TheoryOfGames_Acyclic_Construction
-- name    : TheoryOfGames_Acyclic_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T05:49:41.196652+00:00
-- url     : https://prove2.me/theorems/b3d44801-64dd-447b-8ad0-663da2be3d21
-- title:
--   The inductive construction A_i, B_i, C_i of 65.7.1 and the set V₀ of (65:2)
-- statement:
--   Let $D$ be a set and $\mathcal S$ a relation on $D$. Following 65.7.1, define for every $i = 1, 2, 3, \dots$ three sets $A_i, B_i, C_i \subseteq D$ by induction: $A_1 = D$; if $A_i$ is already known, then
--
--   1. $B_i = A_i^m$, the set of those $y$ in $A_i$ for which $x\mathcal S y$ for no $x$ in $A_i$;
--   2. $C_i$ is the set of those $y$ in $A_i$ for which $x\mathcal S y$ for some $x$ in $B_i$;
--   3. $A_{i+1} = A_i - B_i - C_i$.
--
--   With $i_0$ the smallest $i$ for which $A_i = \ominus$, the book puts
--
--   $$\text{(65:2)}\qquad V_0 = B_1 \cup \cdots \cup B_{i_0 - 1}.$$
--
--   This set is the unique solution when $D$ is finite and $\mathcal S$ acyclic (65:X).
--
--   **Formalization Note** Stages are indexed from $0$: `stageA D S k`, `stageB D S k`, `stageC D S k` are the book's $A_{k+1}, B_{k+1}, C_{k+1}$. `V0 D S` is defined as the union of **all** $B_i$. Once $A_i = \ominus$ every later $A_j$ and $B_j$ is empty, so wherever $i_0$ exists (for finite acyclic $D$, by (65:S)) this union is exactly $B_1 \cup \cdots \cup B_{i_0-1}$; the definition itself makes no finiteness assumption.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 598, 65.7.1; p. 599, 65.7.2, (65:2)

import Mathlib
import Definitions.Def_TheoryOfGames_Acyclic_Solution

namespace TheoryOfGames.Acyclic

/-- 65.7.1: the sets `A_i` of the inductive construction. `A_1 = D`; if `A_i` is known, then
`B_i = A_i^m` (the maxima of `A_i`), `C_i` is the set of those `y` in `A_i` for which `x S y`
for some `x` in `B_i`, and `A_{i+1} = A_i − B_i − C_i`.
Indexing: `stageA D S k` is the book's `A_{k+1}` (so `stageA D S 0 = D = A_1`). -/
def stageA {α : Type*} (D : Set α) (S : α → α → Prop) : ℕ → Set α
  | 0 => D
  | k + 1 =>
    (stageA D S k \ maxima (stageA D S k) S) \
      {y | y ∈ stageA D S k ∧ ∃ x ∈ maxima (stageA D S k) S, S x y}

/-- 65.7.1: `B_i = A_i^m`, the set of those `y` in `A_i` for which `x S y` for no `x` in `A_i`.
`stageB D S k` is the book's `B_{k+1}`. -/
def stageB {α : Type*} (D : Set α) (S : α → α → Prop) (k : ℕ) : Set α :=
  maxima (stageA D S k) S

/-- 65.7.1: `C_i` is the set of those `y` in `A_i` for which `x S y` for some `x` in `B_i`.
`stageC D S k` is the book's `C_{k+1}`. -/
def stageC {α : Type*} (D : Set α) (S : α → α → Prop) (k : ℕ) : Set α :=
  {y | y ∈ stageA D S k ∧ ∃ x ∈ stageB D S k, S x y}

/-- (65:2): `V₀ = B_1 ∪ ⋯ ∪ B_{i₀−1}`, where `i₀` is the smallest `i` with `A_i = ⊖`. Since
`B_i = A_i^m = ⊖` once `A_i = ⊖`, this is the union of all `B_i`, which is how it is written
here (the union over every stage, with no reference to `i₀`). -/
def V0 {α : Type*} (D : Set α) (S : α → α → Prop) : Set α :=
  ⋃ k : ℕ, stageB D S k

end TheoryOfGames.Acyclic


