-- Prove2me | Definitions.Def_StrongPerfectGraph_EvenPrism_Prism
-- name    : StrongPerfectGraph_EvenPrism_Prism
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T03:07:51.216732+00:00
-- url     : https://prove2.me/theorems/f8a9acd7-0633-48b5-b3c8-6970baab1ffd
-- title:
--   Prisms, even prisms, major vertices, and attachments
-- statement:
--   A **prism** consists of three pairwise vertex-disjoint induced paths $R_1,R_2,R_3$ between disjoint triangles $\{a_1,a_2,a_3\}$ and $\{b_1,b_2,b_3\}$; the only edges between distinct paths are the corresponding triangle edges. It is **even** when each path has even length:
--
--   $$|E(R_i)|\equiv 0\pmod 2\qquad(i=1,2,3).$$
--
--   A vertex is **major** for a prism when it has at least two neighbours in each end triangle. A set of prism vertices is **local** when it lies in one path or one end triangle. The module also defines the prism vertices, attachments of an outside set, and completeness to a set. `ContainsEvenPrism` permits other vertices in the ambient graph; `IsEvenPrismGraph` says that the prism covers every vertex.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), https://doi.org/10.4007/annals.2006.164.51, pp. 93 and 119, §7 and §10 definitions of prism, even prism, major, local and attachments

import Definitions.Def_StrongPerfectGraph_EvenPrism_PathHole

namespace StrongPerfectGraph.EvenPrism

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The vertices of three listed paths. -/
def PrismVertices (R : Fin 3 → List V) : Set V :=
  {v | ∃ i, v ∈ R i}

/-- Three induced paths with disjoint vertex sets and exactly the two
triangle edge families between distinct paths. -/
def IsPrism (G : SimpleGraph V) (a b : Fin 3 → V) (R : Fin 3 → List V) : Prop :=
  (∀ i, StrongPerfectGraph.Main.IsInducedPath G (R i) ∧ 2 ≤ (R i).length ∧
    (R i).head? = some (a i) ∧ (R i).getLast? = some (b i)) ∧
  (∀ i j, i ≠ j → ∀ v, v ∈ R i → v ∉ R j) ∧
  (∀ i j, i ≠ j → ∀ u ∈ R i, ∀ v ∈ R j,
    G.Adj u v ↔ (u = a i ∧ v = a j) ∨ (u = b i ∧ v = b j))

/-- All three paths of a prism have even length. -/
def IsEvenPrism (G : SimpleGraph V) (a b : Fin 3 → V) (R : Fin 3 → List V) : Prop :=
  IsPrism G a b R ∧ ∀ i, Even ((R i).length - 1)

/-- An even prism occurs as an induced subgraph. -/
def ContainsEvenPrism (G : SimpleGraph V) : Prop :=
  ∃ a b R, IsEvenPrism G a b R

/-- The whole graph is an even prism. -/
def IsEvenPrismGraph (G : SimpleGraph V) : Prop :=
  ∃ a b R, IsEvenPrism G a b R ∧ PrismVertices R = Set.univ

/-- A set meets at least two vertices of each end triangle. -/
def SaturatesPrism (a b : Fin 3 → V) (X : Set V) : Prop :=
  (∃ i j, i ≠ j ∧ a i ∈ X ∧ a j ∈ X) ∧
  (∃ i j, i ≠ j ∧ b i ∈ X ∧ b j ∈ X)

/-- A vertex is major when its neighbourhood saturates the prism. -/
def IsMajor (G : SimpleGraph V) (a b : Fin 3 → V) (v : V) : Prop :=
  SaturatesPrism a b {x | G.Adj v x}

/-- A set is local when it lies in a single path or one end triangle. -/
def IsLocal (a b : Fin 3 → V) (R : Fin 3 → List V) (X : Set V) : Prop :=
  (∃ i, X ⊆ {v | v ∈ R i}) ∨ X ⊆ Set.range a ∨ X ⊆ Set.range b

/-- A vertex outside the set has every member of it as a neighbour. -/
def CompleteTo (G : SimpleGraph V) (v : V) (X : Set V) : Prop :=
  ∀ x ∈ X, G.Adj v x

/-- The vertices of the prism adjacent to some vertex of F. -/
def Attachments (G : SimpleGraph V) (R : Fin 3 → List V) (F : Set V) : Set V :=
  {x | x ∈ PrismVertices R ∧ ∃ f ∈ F, G.Adj f x}

end StrongPerfectGraph.EvenPrism


