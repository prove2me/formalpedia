-- Prove2me | Definitions.Def_StrongPerfectGraph_Main_IsProperTwoJoin
-- name    : StrongPerfectGraph_Main_IsProperTwoJoin
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T12:38:35.768298+00:00
-- url     : https://prove2.me/theorems/5dce2729-63be-46ce-9d5b-540fb6ce0486
-- title:
--   Proper 2-join
-- statement:
--   A **proper 2-join** partitions $V(G)$ into $X_1,X_2$, with disjoint nonempty attachment sets $A_i,B_i\subseteq X_i$. Across the cut the only edges are all pairs from $A_1\times A_2$ and all pairs from $B_1\times B_2$. Every connected component of $G|X_i$ meets both $A_i$ and $B_i$. If $A_i$ and $B_i$ are singletons and $G|X_i$ is a path joining their members, that path has odd length at least three.
--
--   $$E(G)\cap(X_1\times X_2)=(A_1\times A_2)\cup(B_1\times B_2).$$
--
--   The definition includes the odd-path clause that distinguishes the paper’s proper 2-join from looser 2-join notions. Components are maximal nonempty connected subsets of the induced side.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 53, §1, definition of a proper 2-join

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsInducedPath
import Definitions.Def_StrongPerfectGraph_Main_AdmitsBalancedSkewPartition

namespace StrongPerfectGraph.Main

/-- A maximal nonempty connected subset of `X`. -/
def IsComponentOf {V : Type*} (G : SimpleGraph V) (X C : Set V) : Prop :=
  C.Nonempty ∧ C ⊆ X ∧ IsConnectedSet G C ∧
    ∀ D : Set V, C ⊆ D → D ⊆ X → IsConnectedSet G D → D ⊆ C

/-- The proper 2-join of p. 53, including its special odd-path clause. -/
def IsProperTwoJoin {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ X₁ X₂ A₁ B₁ A₂ B₂ : Set V,
    Disjoint X₁ X₂ ∧ X₁ ∪ X₂ = Set.univ ∧
    A₁.Nonempty ∧ B₁.Nonempty ∧ A₂.Nonempty ∧ B₂.Nonempty ∧
    Disjoint A₁ B₁ ∧ Disjoint A₂ B₂ ∧
    A₁ ⊆ X₁ ∧ B₁ ⊆ X₁ ∧ A₂ ⊆ X₂ ∧ B₂ ⊆ X₂ ∧
    (∀ u ∈ X₁, ∀ v ∈ X₂,
      G.Adj u v ↔ (u ∈ A₁ ∧ v ∈ A₂) ∨ (u ∈ B₁ ∧ v ∈ B₂)) ∧
    (∀ C : Set V, IsComponentOf G X₁ C → (C ∩ A₁).Nonempty ∧ (C ∩ B₁).Nonempty) ∧
    (∀ C : Set V, IsComponentOf G X₂ C → (C ∩ A₂).Nonempty ∧ (C ∩ B₂).Nonempty) ∧
    (∀ (p : List V) (a b : V),
      A₁ = {a} → B₁ = {b} → IsInducedPath G p →
      {v | v ∈ p} = X₁ → p.head? = some a → p.getLast? = some b →
      3 ≤ p.length - 1 ∧ Odd (p.length - 1)) ∧
    (∀ (p : List V) (a b : V),
      A₂ = {a} → B₂ = {b} → IsInducedPath G p →
      {v | v ∈ p} = X₂ → p.head? = some a → p.getLast? = some b →
      3 ≤ p.length - 1 ∧ Odd (p.length - 1))

end StrongPerfectGraph.Main


