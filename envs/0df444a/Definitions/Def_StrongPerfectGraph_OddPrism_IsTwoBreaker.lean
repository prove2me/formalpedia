-- Prove2me | Definitions.Def_StrongPerfectGraph_OddPrism_IsTwoBreaker
-- name    : StrongPerfectGraph_OddPrism_IsTwoBreaker
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T06:29:55.856988+00:00
-- url     : https://prove2.me/theorems/ff19dddd-62a5-487f-a671-0b52335f0716
-- title:
--   2-breaker
-- statement:
--   A pair $(K,Q)$ is a **2-breaker** in $G$ if:
--
--   1. $K=(S=(A,C,B),a_0\text{-}R_0\text{-}b_0)$ is a strongly maximal staircase in $G$;
--   2. $Q\subseteq V(G)\setminus V(K)$ is anticonnected;
--   3. some vertex of $A$ is $Q$-complete, and some vertex of $B$ is $Q$-complete;
--   4. $a_0$ and $b_0$ are not $Q$-complete;
--   5. some vertex of $R_0$ is $Q$-complete.
--
--   If $q$ is a central vertex for a strongly maximal staircase $K$, then $(K,\{q\})$ is a 2-breaker.
--
--   **Formalization Note** $R_0$ is a list whose first and last entries are $a_0$ and $b_0$.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 140, definition of 2-breaker

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsProperTwoJoin
import Definitions.Def_StrongPerfectGraph_OddPrism_IsStaircase

namespace StrongPerfectGraph.OddPrism

/-- `(K, Q)` with `K = (S = (A, C, B), a₀-R₀-b₀)` is a **2-breaker** in `G` (p. 140):
* `K` is a strongly maximal staircase in `G` (`R₀` listed from `a₀` to `b₀`);
* `Q ⊆ V(G) \ V(K)` is anticonnected;
* some vertex of `A` is `Q`-complete, and some vertex of `B` is `Q`-complete;
* `a₀` and `b₀` are not `Q`-complete;
* some vertex of `R₀` is `Q`-complete. -/
def IsTwoBreaker {V : Type*} (G : SimpleGraph V) (A C B : Set V) (r : List V) (Q : Set V) :
    Prop :=
  IsStronglyMaximalStaircase G A C B r ∧
  (∀ q ∈ Q, q ∉ A ∪ B ∪ C ∧ q ∉ r) ∧ StrongPerfectGraph.Main.IsConnectedSet Gᶜ Q ∧
  (∃ a ∈ A, ∀ q ∈ Q, G.Adj a q) ∧ (∃ b ∈ B, ∀ q ∈ Q, G.Adj b q) ∧
  (∃ a₀ b₀, r.head? = some a₀ ∧ r.getLast? = some b₀ ∧
    (∃ q ∈ Q, ¬ G.Adj a₀ q) ∧ (∃ q ∈ Q, ¬ G.Adj b₀ q)) ∧
  (∃ x ∈ r, ∀ q ∈ Q, G.Adj x q)

/-- There is a 2-breaker in `G`. -/
def HasTwoBreaker {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (A C B : Set V) (r : List V) (Q : Set V), IsTwoBreaker G A C B r Q

end StrongPerfectGraph.OddPrism


