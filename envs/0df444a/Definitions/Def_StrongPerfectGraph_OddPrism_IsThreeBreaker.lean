-- Prove2me | Definitions.Def_StrongPerfectGraph_OddPrism_IsThreeBreaker
-- name    : StrongPerfectGraph_OddPrism_IsThreeBreaker
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T06:29:47.341627+00:00
-- url     : https://prove2.me/theorems/a373ef01-d8dd-434f-b580-2aeb3cb161f6
-- title:
--   3-breaker
-- statement:
--   A pair $(K,x)$ is a **3-breaker** in $G$ if $K=(S=(A,C,B),a_0\text{-}R_0\text{-}b_0)$ is a strongly maximal staircase in $G$ and $x\in V(G)\setminus V(K)$ is $B$-complete, not $A$-complete, and not $A$-anticomplete.
--
--   By 13.3 of the paper, under the standing hypotheses of Section 13 a 3-breaker forces a balanced skew partition.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 151, definition of 3-breaker

import Mathlib
import Definitions.Def_StrongPerfectGraph_OddPrism_IsStaircase

namespace StrongPerfectGraph.OddPrism

/-- `(K, x)` with `K = (S = (A, C, B), a₀-R₀-b₀)` is a **3-breaker** in `G` (p. 151): `K` is a
strongly maximal staircase in `G`, and `x ∈ V(G) \ V(K)` is `B`-complete, not `A`-complete and
not `A`-anticomplete. -/
def IsThreeBreaker {V : Type*} (G : SimpleGraph V) (A C B : Set V) (r : List V) (x : V) :
    Prop :=
  IsStronglyMaximalStaircase G A C B r ∧ x ∉ A ∪ B ∪ C ∧ x ∉ r ∧
    (∀ b ∈ B, G.Adj x b) ∧ (∃ a ∈ A, ¬ G.Adj x a) ∧ (∃ a ∈ A, G.Adj x a)

/-- There is a 3-breaker in `G`. -/
def HasThreeBreaker {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (A C B : Set V) (r : List V) (x : V), IsThreeBreaker G A C B r x

end StrongPerfectGraph.OddPrism


