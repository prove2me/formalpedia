-- Prove2me | Definitions.Def_StrongPerfectGraph_OddPrism_IsStepConnectedStrip
-- name    : StrongPerfectGraph_OddPrism_IsStepConnectedStrip
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T05:46:20.272901+00:00
-- url     : https://prove2.me/theorems/47d0dd06-165d-4a68-bd75-343fc135d265
-- title:
--   Strips, rungs, steps and step-connected strips
-- statement:
--   Let $A,B,C$ be disjoint subsets of $V(G)$. The triple $S=(A,C,B)$ is a **strip** if $A$ and $B$ are nonempty and every vertex of $A\cup B\cup C$ belongs to a path between $A$ and $B$ with only its first vertex in $A$, only its last vertex in $B$, and interior in $C$. Such a path is a **rung** of $S$; we write $V(S)=A\cup B\cup C$.
--
--   A **step** is a pair of rungs $a_1\text{-}R_1\text{-}b_1$, $a_2\text{-}R_2\text{-}b_2$ such that $V(R_1)\cap V(R_2)=\emptyset$, $a_1$ is adjacent to $a_2$, $b_1$ is adjacent to $b_2$, and there are no other edges between $V(R_1)$ and $V(R_2)$.
--
--   The strip is **step-connected** if every vertex of $A\cup B\cup C$ is in a step, and for every partition $(X,Y)$ of $A$, or of $B$, into two nonempty sets there is a step $R_1,R_2$ such that $R_1$ has an end in $X$ and $R_2$ has an end in $Y$.
--
--   Step-connected strips are the structure that Section 11 grows out of two paths of a long odd prism.
--
--   **Formalization Note** A rung is an induced path listed from its end in $A$ to its end in $B$. For a partition of $A$ the end in question is the first vertex of the rung, for a partition of $B$ the last vertex.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 112 (strip, rung) and pp. 127–128 (step, step-connected)

import Mathlib
import Definitions.Def_StrongPerfectGraph_OddPrism_IsBerge
import Definitions.Def_StrongPerfectGraph_DoubleSplit_IsStriation

namespace StrongPerfectGraph.OddPrism

/-- A **rung** of the triple `(A, C, B)` (p. 112): a path of `G` whose first vertex is in `A`,
whose last vertex is in `B`, and all of whose other vertices are in `C`. (With `A, B, C`
pairwise disjoint, only its first vertex is in `A` and only its last vertex is in `B`.) -/
def IsRung {V : Type*} (G : SimpleGraph V) (A C B : Set V) (r : List V) : Prop :=
  IsInducedPath G r ∧
    ∃ a b, r.head? = some a ∧ r.getLast? = some b ∧ a ∈ A ∧ b ∈ B ∧
      ∀ x ∈ r, x ≠ a → x ≠ b → x ∈ C

/-- A **step** of the strip `(A, C, B)` (p. 127): two vertex-disjoint rungs `a₁-R₁-b₁` and
`a₂-R₂-b₂` such that `a₁` is adjacent to `a₂`, `b₁` is adjacent to `b₂`, and there are no other
edges between `V(R₁)` and `V(R₂)`. -/
def IsStep {V : Type*} (G : SimpleGraph V) (A C B : Set V) (r₁ r₂ : List V) : Prop :=
  IsRung G A C B r₁ ∧ IsRung G A C B r₂ ∧
    (∀ x ∈ r₁, x ∉ r₂) ∧
    ∀ x ∈ r₁, ∀ y ∈ r₂,
      G.Adj x y ↔
        (r₁.head? = some x ∧ r₂.head? = some y) ∨
        (r₁.getLast? = some x ∧ r₂.getLast? = some y)

/-- The strip `(A, C, B)` is **step-connected** (p. 128): it is a strip, every vertex of
`A ∪ B ∪ C` lies in a step, and for every partition `(X, Y)` of `A` (respectively of `B`) into
two nonempty sets there is a step `R₁, R₂` such that `R₁` has an end in `X` and `R₂` has an end
in `Y`. -/
def IsStepConnected {V : Type*} (G : SimpleGraph V) (A C B : Set V) : Prop :=
  StrongPerfectGraph.DoubleSplit.IsStrip G A C B ∧
    (∀ v ∈ A ∪ B ∪ C, ∃ r₁ r₂, IsStep G A C B r₁ r₂ ∧ (v ∈ r₁ ∨ v ∈ r₂)) ∧
    (∀ X Y : Set V, X.Nonempty → Y.Nonempty → Disjoint X Y → X ∪ Y = A →
      ∃ r₁ r₂, IsStep G A C B r₁ r₂ ∧
        (∃ x ∈ X, r₁.head? = some x) ∧ (∃ y ∈ Y, r₂.head? = some y)) ∧
    (∀ X Y : Set V, X.Nonempty → Y.Nonempty → Disjoint X Y → X ∪ Y = B →
      ∃ r₁ r₂, IsStep G A C B r₁ r₂ ∧
        (∃ x ∈ X, r₁.getLast? = some x) ∧ (∃ y ∈ Y, r₂.getLast? = some y))

end StrongPerfectGraph.OddPrism


