-- Prove2me | Definitions.Def_StrongPerfectGraph_OddPrism_StaircaseVertexTypes
-- name    : StrongPerfectGraph_OddPrism_StaircaseVertexTypes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T06:28:56.379992+00:00
-- url     : https://prove2.me/theorems/5c737bd4-7180-4711-9990-b93ffa1d3091
-- title:
--   Minor, major, left- and right-diagonal and central vertices of a staircase
-- statement:
--   Let $K=(S=(A,C,B),a_0\text{-}R_0\text{-}b_0)$ be a staircase in $G$. With respect to $K$:
--
--   1. a set $X\subseteq V(K)$ is **local** if it is a subset of one of $V(S)$, $V(R_0)$, $A\cup\{a_0\}$, $B\cup\{b_0\}$;
--   2. $v\in V(G)\setminus V(K)$ is **minor** if its set of neighbours in $V(K)$ is local;
--   3. $v\in V(G)\setminus V(K)$ is **major** if it has neighbours in all of $A$, $B$ and $V(R_0)$;
--   4. $v\in V(G)\setminus V(K)$ is **left-diagonal** if it is $(A\cup\{b_0\})$-complete, and **right-diagonal** if it is $(B\cup\{a_0\})$-complete;
--   5. $v\in V(G)\setminus V(K)$ is **central** if it is $(A\cup B)$-complete and nonadjacent to both $a_0$ and $b_0$.
--
--   These types classify the vertices outside a maximal staircase (12.1 of the paper).
--
--   **Formalization Note** The ends $a_0,b_0$ of $R_0$ are passed explicitly; each predicate includes $v\notin V(K)$.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 134, definitions of local, minor, major, left-/right-diagonal and central

import Mathlib
import Definitions.Def_StrongPerfectGraph_OddPrism_IsStaircase

namespace StrongPerfectGraph.OddPrism

/-! Vertex types with respect to a staircase `K = (S = (A, C, B), a₀-R₀-b₀)` (p. 134), where
`R₀` is the list `r` from `a₀` to `b₀` and `V(K) = V(R₀) ∪ A ∪ B ∪ C`. -/

/-- `X ⊆ V(K)` is **local** with respect to `K`: `X` is a subset of one of `V(S)`, `V(R₀)`,
`A ∪ {a₀}`, `B ∪ {b₀}`. -/
def IsLocalStaircase {V : Type*} (A C B : Set V) (r : List V) (a₀ b₀ : V) (X : Set V) :
    Prop :=
  X ⊆ A ∪ B ∪ C ∨ X ⊆ {x | x ∈ r} ∨ X ⊆ A ∪ {a₀} ∨ X ⊆ B ∪ {b₀}

/-- `v ∈ V(G) \ V(K)` is **minor** if its set of neighbours in `V(K)` is local. -/
def IsMinor {V : Type*} (G : SimpleGraph V) (A C B : Set V) (r : List V) (a₀ b₀ v : V) :
    Prop :=
  v ∉ A ∪ B ∪ C ∧ v ∉ r ∧
    IsLocalStaircase A C B r a₀ b₀ {x | (x ∈ A ∪ B ∪ C ∨ x ∈ r) ∧ G.Adj v x}

/-- `v ∈ V(G) \ V(K)` is **major** if it has neighbours in all of `A`, `B` and `V(R₀)`. -/
def IsMajor {V : Type*} (G : SimpleGraph V) (A C B : Set V) (r : List V) (v : V) : Prop :=
  v ∉ A ∪ B ∪ C ∧ v ∉ r ∧
    (∃ a ∈ A, G.Adj v a) ∧ (∃ b ∈ B, G.Adj v b) ∧ (∃ x ∈ r, G.Adj v x)

/-- `v ∈ V(G) \ V(K)` is **left-diagonal** if it is `(A ∪ {b₀})`-complete. -/
def IsLeftDiagonal {V : Type*} (G : SimpleGraph V) (A C B : Set V) (r : List V) (b₀ v : V) :
    Prop :=
  v ∉ A ∪ B ∪ C ∧ v ∉ r ∧ ∀ x ∈ A ∪ {b₀}, G.Adj v x

/-- `v ∈ V(G) \ V(K)` is **right-diagonal** if it is `(B ∪ {a₀})`-complete. -/
def IsRightDiagonal {V : Type*} (G : SimpleGraph V) (A C B : Set V) (r : List V) (a₀ v : V) :
    Prop :=
  v ∉ A ∪ B ∪ C ∧ v ∉ r ∧ ∀ x ∈ B ∪ {a₀}, G.Adj v x

/-- `v ∈ V(G) \ V(K)` is **central** if it is `(A ∪ B)`-complete and nonadjacent to both
`a₀` and `b₀`. -/
def IsCentral {V : Type*} (G : SimpleGraph V) (A C B : Set V) (r : List V) (a₀ b₀ v : V) :
    Prop :=
  v ∉ A ∪ B ∪ C ∧ v ∉ r ∧ (∀ x ∈ A ∪ B, G.Adj v x) ∧ ¬ G.Adj v a₀ ∧ ¬ G.Adj v b₀

end StrongPerfectGraph.OddPrism


