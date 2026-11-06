-- Prove2me | Definitions.Def_QEC_Locality_Graph_Core
-- name    : QEC_Locality_Graph_Core
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:53:06.547401+00:00
-- url     : https://prove2.me/theorems/560ba2d8-504e-4573-8536-120aa74875e4
-- title:
--   Core
-- statement:
--   Definitions and structural lemmas for Core, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/Core.lean

import Mathlib
set_option autoImplicit false
namespace QEC.Locality
universe u
structure ConnectivityGraph (ι : Type u) [Fintype ι] where
  adjacent : ι → ι → Prop
  symmetric : ∀ ⦃i j : ι⦄, adjacent i j → adjacent j i
  loopless : ∀ i : ι, ¬ adjacent i i
def inducedSubgraph {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (vertices : Finset ι) :
    ConnectivityGraph {i : ι // i ∈ vertices} where
  adjacent x y := G.adjacent x.1 y.1
  symmetric := by
    intro x y hxy
    exact G.symmetric hxy
  loopless := by
    intro x hxx
    exact G.loopless x.1 hxx
def NoEdgeBetween {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (left right : Finset ι) : Prop :=
  ∀ ⦃x : ι⦄, x ∈ left → ∀ ⦃y : ι⦄, y ∈ right → ¬ G.adjacent x y
def TwoThirdsBalancedPartitionAfterDeleting {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (vertices left separator right : Finset ι) : Prop :=
  separator ⊆ vertices ∧
    left ∪ right = vertices \ separator ∧
    Disjoint left right ∧
    3 * left.card ≤ 2 * vertices.card ∧
    3 * right.card ≤ 2 * vertices.card ∧
    NoEdgeBetween G left right
def IsTwoThirdsBalancedVertexSeparator {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (vertices separator : Finset ι) : Prop :=
  ∃ left right : Finset ι,
    TwoThirdsBalancedPartitionAfterDeleting G vertices left separator right
end QEC.Locality


