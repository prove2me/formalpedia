-- Prove2me | Definitions.Def_FoucaudIdentification_DiameterTwo_IntervalModel
-- name    : FoucaudIdentification_DiameterTwo_IntervalModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-31T02:20:18.60772+00:00
-- url     : https://prove2.me/theorems/904ae0e2-d082-47da-97b7-51af3a426e9c
-- title:
--   Interval diagrams and induced module placements
-- statement:
--   An interval model assigns ordered real endpoints to every vertex. Intersection and containment are defined by their endpoint inequalities. The model represents a graph when exactly the distinct intersecting intervals are adjacent. An induced gadget copy is an injective vertex map preserving and reflecting adjacency. Its placement condition says each external interval either contains all gadget intervals or misses all of them.
-- source:
--   Foucaud et al., arXiv:1405.2424v3, pp. 2, 5–6, Definitions 6 and 8. https://arxiv.org/abs/1405.2424v3

import Definitions.Def_FoucaudIdentification_DiameterTwo_GraphClasses

namespace FoucaudIdentification.DiameterTwo

structure IntervalModel (V : Type) where
  left : V → ℝ
  right : V → ℝ
  ordered : ∀ v, left v ≤ right v

def IntervalModel.meets {V : Type} (I : IntervalModel V) (u v : V) : Prop :=
  I.left u ≤ I.right v ∧ I.left v ≤ I.right u

def IntervalModel.contains {V : Type} (I : IntervalModel V) (u v : V) : Prop :=
  I.left u ≤ I.left v ∧ I.right v ≤ I.right u

def IntervalModel.graph {V : Type} (I : IntervalModel V) : SimpleGraph V :=
  SimpleGraph.fromRel I.meets

def IntervalModel.represents {V : Type} (I : IntervalModel V) (G : SimpleGraph V) : Prop :=
  ∀ u v, G.Adj u v ↔ u ≠ v ∧ I.meets u v

/-- External intervals contain the whole local diagram or miss every interval. -/
def IntervalModule {n q : ℕ} (I : IntervalModel (Fin n)) (e : Fin q ↪ Fin n) : Prop :=
  ∀ x, x ∉ Set.range e →
    (∀ y, I.contains x (e y)) ∨ (∀ y, ¬ I.meets x (e y))

def InducedCopy {n q : ℕ} (D : SimpleGraph (Fin q)) (G : SimpleGraph (Fin n))
    (e : Fin q ↪ Fin n) : Prop := ∀ x y, G.Adj (e x) (e y) ↔ D.Adj x y

def copyVertices {n q : ℕ} (e : Fin q ↪ Fin n) : Finset (Fin n) := Finset.univ.map e

end FoucaudIdentification.DiameterTwo


