-- Prove2me | Definitions.Def_FoucaudIdentification_DiameterTwo_GraphClasses
-- name    : FoucaudIdentification_DiameterTwo_GraphClasses
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-31T02:19:44.697336+00:00
-- url     : https://prove2.me/theorems/7b0f2089-9966-4433-a1f8-6c9ba1cf3847
-- title:
--   Split graphs, segment intersection graphs and diameter exactly two
-- statement:
--   A split graph admits a partition into a clique and an independent set. A permutation graph is represented by straight segments between two parallel lines; two segments meet when their horizontal coordinates agree at some common height between the lines. Equal or shared endpoints are allowed. Interval graphs use the referenced closed-interval intersection definition. Diameter exactly two requires paths of length at most two between every pair and at least one distinct nonadjacent pair. Graph classes range over all finite labeled simple graphs.
-- source:
--   Foucaud et al., arXiv:1405.2424v3, pp. 2–3 and p. 13, graph classes and Corollary 20. https://arxiv.org/abs/1405.2424v3

import Definitions.Def_AppliedComb_Graphs_IsIntervalGraph

namespace FoucaudIdentification.DiameterTwo

/-- A segment diagram has one endpoint on each of two parallel lines. -/
structure SegmentDiagram (V : Type) where
  bottom : V → ℝ
  top : V → ℝ

/-- Coincidence of the horizontal coordinates at a common height. -/
def SegmentDiagram.meets {V : Type} (D : SegmentDiagram V) (u v : V) : Prop :=
  ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
    (1 - t) * D.bottom u + t * D.top u = (1 - t) * D.bottom v + t * D.top v

def IsPermutation {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ D : SegmentDiagram V, ∀ u v, u ≠ v → (G.Adj u v ↔ D.meets u v)

def IsSplit {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ K : Set V,
    (∀ u ∈ K, ∀ v ∈ K, u ≠ v → G.Adj u v) ∧
    (∀ u ∉ K, ∀ v ∉ K, ¬ G.Adj u v)

/-- Connected diameter exactly two, including an explicit distance-two pair. -/
def DiameterTwo {V : Type} (G : SimpleGraph V) : Prop :=
  (∀ u v, u = v ∨ G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj w v) ∧
    ∃ u v, u ≠ v ∧ ¬ G.Adj u v

/-- Classes of finite labeled graphs. No order bound is imposed. -/
abbrev GraphClass := (n : ℕ) → SimpleGraph (Fin n) → Prop

def splitClass : GraphClass := fun _ G => IsSplit G
def intervalClass : GraphClass := fun _ G => AppliedComb.Graphs.IsIntervalGraph G
def permutationClass : GraphClass := fun _ G => IsPermutation G
def atDiameterTwo (C : GraphClass) : GraphClass := fun n G => C n G ∧ DiameterTwo G

end FoucaudIdentification.DiameterTwo


