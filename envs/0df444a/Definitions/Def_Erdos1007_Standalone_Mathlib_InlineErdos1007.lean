-- Prove2me | Definitions.Def_Erdos1007_Standalone_Mathlib_InlineErdos1007
-- name    : Erdos1007_Standalone_Mathlib_InlineErdos1007
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T06:52:56.907713+00:00
-- url     : https://prove2.me/theorems/809231ca-cdbf-4093-acfc-96e992d8840a
-- title:
--   Inline Erdos1007
-- statement:
--   Definitions and structural lemmas for Inline Erdos1007, from Dishant Shah (Dishah3241/Erdos1007; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Unit-distance graphs of dimension four with nine edges (Erdos Problem 1007 extremal half) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Standalone/Mathlib/InlineErdos1007.lean

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Finite
set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace Erdos1007.Standalone.Mathlib.InlineErdos1007
open scoped RealInnerProductSpace
def UnitDistanceEmbeddable {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ f : V → EuclideanSpace ℝ (Fin n), Function.Injective f ∧
    ∀ u v : V, G.Adj u v → dist (f u) (f v) = 1
def UnitDistanceEmbeddable.separating : Prop :=
  ∃ (V : Type) (G : SimpleGraph V) (n : ℕ) (f : V → EuclideanSpace ℝ (Fin n)),
    UnitDistanceEmbeddable G n ∧
      Function.Injective f ∧ (∀ u v : V, G.Adj u v → dist (f u) (f v) = 1) ∧
        ∃ u v : V, u ≠ v ∧ ¬ G.Adj u v ∧ dist (f u) (f v) = 1
def HasDimension {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  IsLeast {m | UnitDistanceEmbeddable G m} n
def HasDimension.separating : Prop :=
  ∃ (V : Type) (G : SimpleGraph V),
    (∃ u v : V, G.Adj u v) ∧ UnitDistanceEmbeddable G 4 ∧ ¬ HasDimension G 4
def DimensionFourExtremal : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    HasDimension G 4 → G.edgeSet.ncard = 9 → (∀ v : Fin n, ∃ w : Fin n, G.Adj v w) →
      Nonempty (G ≃g completeBipartiteGraph (Fin 3) (Fin 3))
def DimensionFourExtremal.drop2 : Prop :=
  ¬ ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.edgeSet.ncard = 9 → (∀ v : Fin n, ∃ w : Fin n, G.Adj v w) →
        Nonempty (G ≃g completeBipartiteGraph (Fin 3) (Fin 3))
def DimensionFourExtremal.drop3 : Prop :=
  ¬ ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      HasDimension G 4 → (∀ v : Fin n, ∃ w : Fin n, G.Adj v w) →
        Nonempty (G ≃g completeBipartiteGraph (Fin 3) (Fin 3))
def DimensionFourExtremal.drop4 : Prop :=
  ¬ ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      HasDimension G 4 → G.edgeSet.ncard = 9 →
        Nonempty (G ≃g completeBipartiteGraph (Fin 3) (Fin 3))
def DimensionFourExtremal.witness : Prop :=
  ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
    HasDimension G 4 ∧ G.edgeSet.ncard = 9 ∧ ∀ v : Fin n, ∃ w : Fin n, G.Adj v w
end Erdos1007.Standalone.Mathlib.InlineErdos1007


