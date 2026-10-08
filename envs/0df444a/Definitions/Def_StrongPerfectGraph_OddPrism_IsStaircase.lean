-- Prove2me | Definitions.Def_StrongPerfectGraph_OddPrism_IsStaircase
-- name    : StrongPerfectGraph_OddPrism_IsStaircase
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T06:10:31.440993+00:00
-- url     : https://prove2.me/theorems/e0b4a8b5-5517-42e5-a474-541aa054f253
-- title:
--   Left- and right-stars, banisters, and (strongly) maximal staircases
-- statement:
--   Let $S=(A,C,B)$ be a step-connected strip in $G$. A vertex $v\in V(G)\setminus(A\cup B\cup C)$ is a **left-star** if it is complete to $A$ and anticomplete to $B\cup C$, and a **right-star** if it is complete to $B$ and anticomplete to $A\cup C$. A **banister** is a path $a\text{-}R\text{-}b$ of $G\setminus(A\cup B\cup C)$ such that $a$ is a left-star, $b$ is a right-star, and there are no edges between the interior of $R$ and $V(S)$ (the left-star end is listed first).
--
--   If $a_0\text{-}R_0\text{-}b_0$ is a banister of length at least $3$, the pair $K=(S,R_0)$ is a **staircase**, with $V(K)=V(R_0)\cup V(S)$. The staircase is **maximal** if there is no staircase $(S'=(A',C',B'),a_0'\text{-}R_0'\text{-}b_0')$ with $A\subseteq A'$, $B\subseteq B'$, $C\subseteq C'$ and $V(S)\subsetneq V(S')$. It is **strongly maximal** if it is maximal and, in addition, either $C\neq\emptyset$ or there is no staircase $(S',R')$ in $\overline{G}$ with $V(S)\subsetneq V(S')$.
--
--   Staircases are the main bookkeeping device of Sections 12 and 13.
--
--   **Formalization Note** The banister is a list from $a_0$ to $b_0$. In $\overline{G}$, steps, stars and banisters are the same predicates applied to `Gᶜ`.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 128 (left-star, right-star, banister), p. 133 (staircase, maximal), p. 140 (strongly maximal)

import Mathlib
import Definitions.Def_StrongPerfectGraph_OddPrism_IsBerge
import Definitions.Def_StrongPerfectGraph_OddPrism_IsStepConnectedStrip

namespace StrongPerfectGraph.OddPrism

/-- `v` is a **left-star** for the strip `(A, C, B)` (p. 128): `v ∉ A ∪ B ∪ C`, `v` is complete
to `A` and anticomplete to `B ∪ C`. -/
def IsLeftStar {V : Type*} (G : SimpleGraph V) (A C B : Set V) (v : V) : Prop :=
  v ∉ A ∪ B ∪ C ∧ (∀ a ∈ A, G.Adj v a) ∧ ∀ x ∈ B ∪ C, ¬ G.Adj v x

/-- `v` is a **right-star** for the strip `(A, C, B)` (p. 128): `v ∉ A ∪ B ∪ C`, `v` is complete
to `B` and anticomplete to `A ∪ C`. -/
def IsRightStar {V : Type*} (G : SimpleGraph V) (A C B : Set V) (v : V) : Prop :=
  v ∉ A ∪ B ∪ C ∧ (∀ b ∈ B, G.Adj v b) ∧ ∀ x ∈ A ∪ C, ¬ G.Adj v x

/-- A **banister** `a-R-b` with respect to the strip `(A, C, B)` (p. 128): a path of
`G \ (A ∪ B ∪ C)`, listed from `a` to `b`, such that `a` is a left-star, `b` is a right-star,
and there are no edges between the interior of `R` and `A ∪ B ∪ C`. -/
def IsBanister {V : Type*} (G : SimpleGraph V) (A C B : Set V) (r : List V) : Prop :=
  IsInducedPath G r ∧ (∀ x ∈ r, x ∉ A ∪ B ∪ C) ∧
    ∃ a b, r.head? = some a ∧ r.getLast? = some b ∧
      IsLeftStar G A C B a ∧ IsRightStar G A C B b ∧
      ∀ x ∈ r, x ≠ a → x ≠ b → ∀ s ∈ A ∪ B ∪ C, ¬ G.Adj x s

/-- A **staircase** `K = (S = (A, C, B), a₀-R₀-b₀)` (p. 133): `S` is a step-connected strip and
`R₀` (listed from `a₀` to `b₀`) is a banister of length at least `3`.
Its vertex set is `V(K) = V(R₀) ∪ A ∪ B ∪ C`. -/
def IsStaircase {V : Type*} (G : SimpleGraph V) (A C B : Set V) (r : List V) : Prop :=
  IsStepConnected G A C B ∧ IsBanister G A C B r ∧ 3 ≤ r.length - 1

/-- A staircase `(S = (A, C, B), a₀-R₀-b₀)` is **maximal** (p. 133) if there is no staircase
`(S' = (A', C', B'), a₀'-R₀'-b₀')` with `A ⊆ A'`, `B ⊆ B'`, `C ⊆ C'` and `V(S) ⊊ V(S')`. -/
def IsMaximalStaircase {V : Type*} (G : SimpleGraph V) (A C B : Set V) (r : List V) : Prop :=
  IsStaircase G A C B r ∧
    ¬ ∃ (A' C' B' : Set V) (r' : List V), IsStaircase G A' C' B' r' ∧
      A ⊆ A' ∧ B ⊆ B' ∧ C ⊆ C' ∧ A ∪ B ∪ C ⊂ A' ∪ B' ∪ C'

/-- A staircase `(S = (A, C, B), a₀-R₀-b₀)` is **strongly maximal** (p. 140) if it is maximal
and, in addition, either `C ≠ ∅` or there is no staircase `(S', R')` in the complement `Gᶜ`
with `V(S) ⊊ V(S')`. -/
def IsStronglyMaximalStaircase {V : Type*} (G : SimpleGraph V) (A C B : Set V)
    (r : List V) : Prop :=
  IsMaximalStaircase G A C B r ∧
    (C.Nonempty ∨
      ¬ ∃ (A' C' B' : Set V) (r' : List V), IsStaircase Gᶜ A' C' B' r' ∧
        A ∪ B ∪ C ⊂ A' ∪ B' ∪ C')

end StrongPerfectGraph.OddPrism


