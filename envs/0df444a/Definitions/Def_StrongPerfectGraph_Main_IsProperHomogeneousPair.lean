-- Prove2me | Definitions.Def_StrongPerfectGraph_Main_IsProperHomogeneousPair
-- name    : StrongPerfectGraph_Main_IsProperHomogeneousPair
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T12:06:06.360094+00:00
-- url     : https://prove2.me/theorems/1fd65872-fa4d-4f80-8c98-a72431a63435
-- title:
--   Proper homogeneous pair
-- statement:
--   A **proper homogeneous pair** consists of disjoint nonempty vertex sets $A,B$. Let $A_1$ and $A_2$ be the vertices complete and anticomplete to $A$, and define $B_1,B_2$ similarly. The four outside classes satisfy
--
--   $$A_1\cup A_2=B_1\cup B_2=V(G)\setminus(A\cup B),\qquad A_i\cap B_j\ne\varnothing\quad(i,j\in\{1,2\}).$$
--
--   Thus every outside vertex is either complete or anticomplete to each part, and all four combinations occur. The equalities also imply that every vertex of either part has both a neighbor and a nonneighbor in the other part. This is the paper’s strengthened homogeneous-pair decomposition.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 53, §1, definition of a proper homogeneous pair

import Mathlib

namespace StrongPerfectGraph.Main

/-- Every vertex in `X` is adjacent to `v`. -/
def IsCompleteTo {V : Type*} (G : SimpleGraph V) (v : V) (X : Set V) : Prop :=
  ∀ x ∈ X, G.Adj v x

/-- No vertex in `X` is adjacent to `v`. -/
def IsAnticompleteTo {V : Type*} (G : SimpleGraph V) (v : V) (X : Set V) : Prop :=
  ∀ x ∈ X, ¬ G.Adj v x

/-- A proper homogeneous pair, using the four outside classes of p. 53. -/
def IsProperHomogeneousPair {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ A B : Set V,
    A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
    let A₁ := {v | IsCompleteTo G v A}
    let A₂ := {v | IsAnticompleteTo G v A}
    let B₁ := {v | IsCompleteTo G v B}
    let B₂ := {v | IsAnticompleteTo G v B}
    A₁ ∪ A₂ = (A ∪ B)ᶜ ∧ B₁ ∪ B₂ = (A ∪ B)ᶜ ∧
      (A₁ ∩ B₁).Nonempty ∧ (A₁ ∩ B₂).Nonempty ∧
      (A₂ ∩ B₁).Nonempty ∧ (A₂ ∩ B₂).Nonempty

end StrongPerfectGraph.Main


