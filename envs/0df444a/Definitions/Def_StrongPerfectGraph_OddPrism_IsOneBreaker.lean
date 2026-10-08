-- Prove2me | Definitions.Def_StrongPerfectGraph_OddPrism_IsOneBreaker
-- name    : StrongPerfectGraph_OddPrism_IsOneBreaker
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T06:29:23.270305+00:00
-- url     : https://prove2.me/theorems/e30a6944-961c-4c76-a233-9303e7059bca
-- title:
--   1-breaker
-- statement:
--   A triple $(S,F,Q)$ is a **1-breaker** in $G$ if:
--
--   1. $S=(A,C,B)$ is a step-connected strip in $G$;
--   2. $F\subseteq V(G)\setminus V(S)$ is connected, there are no edges between $F$ and $V(S)$, and there are a left-star and a right-star, both with neighbours in $F$;
--   3. $Q\subseteq V(G)\setminus(V(S)\cup F)$ is anticonnected;
--   4. some vertex of $A$ has a nonneighbour in $Q$, and so does some vertex of $B$;
--   5. every vertex of $Q$ has a neighbour in $F$ and a neighbour in $A\cup B\cup C$;
--   6. some left-star with a neighbour in $F$ is $Q$-complete;
--   7. no vertex of $Q$ is a left-star.
--
--   By 11.5 of the paper, a Berge graph with no appearance of $K_4$ and no even prism that contains a 1-breaker admits a balanced skew partition.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), pp. 130–131, definition of 1-breaker

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsProperTwoJoin
import Definitions.Def_StrongPerfectGraph_OddPrism_IsStaircase

namespace StrongPerfectGraph.OddPrism

/-- `(S, F, Q)` with `S = (A, C, B)` is a **1-breaker** in `G` (pp. 130–131):
* `S` is a step-connected strip in `G`;
* `F ⊆ V(G) \ V(S)` is connected, there are no edges between `F` and `V(S)`, and there are a
  left-star and a right-star, both with neighbours in `F`;
* `Q ⊆ V(G) \ (V(S) ∪ F)` is anticonnected;
* some vertex of `A` has a nonneighbour in `Q`, and so does some vertex of `B`;
* every vertex of `Q` has a neighbour in `F` and a neighbour in `A ∪ B ∪ C`;
* some left-star with a neighbour in `F` is `Q`-complete;
* no vertex of `Q` is a left-star. -/
def IsOneBreaker {V : Type*} (G : SimpleGraph V) (A C B F Q : Set V) : Prop :=
  IsStepConnected G A C B ∧
  (F ⊆ (A ∪ B ∪ C)ᶜ ∧ StrongPerfectGraph.Main.IsConnectedSet G F ∧ (∀ f ∈ F, ∀ s ∈ A ∪ B ∪ C, ¬ G.Adj f s) ∧
    (∃ u, IsLeftStar G A C B u ∧ ∃ f ∈ F, G.Adj u f) ∧
    (∃ u, IsRightStar G A C B u ∧ ∃ f ∈ F, G.Adj u f)) ∧
  (Q ⊆ (A ∪ B ∪ C ∪ F)ᶜ ∧ StrongPerfectGraph.Main.IsConnectedSet Gᶜ Q) ∧
  ((∃ a ∈ A, ∃ q ∈ Q, ¬ G.Adj a q) ∧ (∃ b ∈ B, ∃ q ∈ Q, ¬ G.Adj b q)) ∧
  (∀ q ∈ Q, (∃ f ∈ F, G.Adj q f) ∧ ∃ s ∈ A ∪ B ∪ C, G.Adj q s) ∧
  (∃ u, IsLeftStar G A C B u ∧ (∃ f ∈ F, G.Adj u f) ∧ ∀ q ∈ Q, G.Adj u q) ∧
  (∀ q ∈ Q, ¬ IsLeftStar G A C B q)

/-- There is a 1-breaker in `G`. -/
def HasOneBreaker {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ A C B F Q : Set V, IsOneBreaker G A C B F Q

end StrongPerfectGraph.OddPrism


