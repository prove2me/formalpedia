-- Prove2me | Definitions.Def_StrongPerfectGraph_EvenPrism_Decompositions
-- name    : StrongPerfectGraph_EvenPrism_Decompositions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T03:08:00.495237+00:00
-- url     : https://prove2.me/theorems/d2f9dbf2-9a9a-47f2-a742-db911cf81ee3
-- title:
--   Proper 2-joins
-- statement:
--   A **proper 2-join** divides the graph into two sides $X_1,X_2$ with disjoint, nonempty attachment sets $A_i,B_i\subseteq X_i$. Its cross edges are exactly the complete pairs $A_1$ to $A_2$ and $B_1$ to $B_2$; every component of each side meets both attachment sets. A side that is itself a path between singleton attachment sets must have odd length at least three. Together with balanced skew partitions, these are the decomposition outcomes of Theorem 10.6.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), https://doi.org/10.4007/annals.2006.164.51, p. 53, §1 definition of proper 2-join

import Definitions.Def_StrongPerfectGraph_EvenPrism_PathHole
import Definitions.Def_StrongPerfectGraph_Main_AdmitsBalancedSkewPartition

namespace StrongPerfectGraph.EvenPrism

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Each component of G induced on X meets A. -/
def EveryComponentMeets (G : SimpleGraph V) (X A : Set V) : Prop :=
  ∀ (x : V) (hx : x ∈ X), ∃ (a : V) (ha : a ∈ A) (hax : a ∈ X),
    (G.induce X).Reachable ⟨x, hx⟩ ⟨a, hax⟩

/-- The special side of a 2-join: its attachment sets are singleton
and the whole side is one path between their members. -/
def IsPathSide (G : SimpleGraph V) (X A B : Set V) : Prop :=
  Set.Subsingleton A ∧ Set.Subsingleton B ∧
  ∃ p : List V, StrongPerfectGraph.Main.IsInducedPath G p ∧ {v | v ∈ p} = X ∧
    ((∃ a ∈ A, ∃ b ∈ B, p.head? = some a ∧ p.getLast? = some b) ∨
     (∃ b ∈ B, ∃ a ∈ A, p.head? = some b ∧ p.getLast? = some a))

/-- The proper 2-join of p. 53, including its component and odd-path clauses. -/
def AdmitsProperTwoJoin (G : SimpleGraph V) : Prop :=
  ∃ X₁ X₂ A₁ B₁ A₂ B₂ : Set V,
    Disjoint X₁ X₂ ∧ X₁ ∪ X₂ = Set.univ ∧
    A₁.Nonempty ∧ B₁.Nonempty ∧ A₂.Nonempty ∧ B₂.Nonempty ∧
    Disjoint A₁ B₁ ∧ Disjoint A₂ B₂ ∧
    A₁ ⊆ X₁ ∧ B₁ ⊆ X₁ ∧ A₂ ⊆ X₂ ∧ B₂ ⊆ X₂ ∧
    (∀ u ∈ X₁, ∀ v ∈ X₂,
      (G.Adj u v ↔ (u ∈ A₁ ∧ v ∈ A₂) ∨ (u ∈ B₁ ∧ v ∈ B₂))) ∧
    EveryComponentMeets G X₁ A₁ ∧ EveryComponentMeets G X₁ B₁ ∧
    EveryComponentMeets G X₂ A₂ ∧ EveryComponentMeets G X₂ B₂ ∧
    (IsPathSide G X₁ A₁ B₁ →
      ∀ p : List V, StrongPerfectGraph.Main.IsInducedPath G p → {v | v ∈ p} = X₁ →
        3 ≤ p.length - 1 ∧ Odd (p.length - 1)) ∧
    (IsPathSide G X₂ A₂ B₂ →
      ∀ p : List V, StrongPerfectGraph.Main.IsInducedPath G p → {v | v ∈ p} = X₂ →
        3 ≤ p.length - 1 ∧ Odd (p.length - 1))

end StrongPerfectGraph.EvenPrism


