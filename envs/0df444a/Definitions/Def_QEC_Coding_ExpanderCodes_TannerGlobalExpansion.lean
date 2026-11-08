-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_TannerGlobalExpansion
-- name    : QEC_Coding_ExpanderCodes_TannerGlobalExpansion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T07:35:18.404388+00:00
-- url     : https://prove2.me/theorems/79f0f61f-a266-4a27-82c3-39f5aa627be5
-- title:
--   Tanner Global Expansion
-- statement:
--   Definitions and structural lemmas for Tanner Global Expansion, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGlobalExpansion.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerBlockWeight
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
def adjacencyGraph (label : W → G) :
    SmallSetExpansion.WeightedGraph (VertexIndex G) :=
  fun v u =>
    (Finset.univ.filter fun a : W => horizontalNeighbor label v a = u).card +
      (Finset.univ.filter fun b : W => verticalNeighbor label v b = u).card
def faceSquareGraph (label : W → G) :
    SmallSetExpansion.WeightedGraph (VertexIndex G) :=
  fun v u =>
    (Finset.univ.filter fun p : W × W =>
      verticalNeighbor label (horizontalNeighbor label v p.1) p.2 = u).card
noncomputable def horizontalDirectionsInto (label : W → G)
    (L : Finset (VertexIndex G)) (v : VertexIndex G) : Finset W := by
  classical
  exact Finset.univ.filter fun a => horizontalNeighbor label v a ∈ L
noncomputable def verticalDirectionsInto (label : W → G)
    (L : Finset (VertexIndex G)) (v : VertexIndex G) : Finset W := by
  classical
  exact Finset.univ.filter fun b => verticalNeighbor label v b ∈ L
noncomputable def horizontalDirectionsOutside (label : W → G)
    (L : Finset (VertexIndex G)) (v : VertexIndex G) : Finset W := by
  classical
  exact Finset.univ.filter fun a => horizontalNeighbor label v a ∉ L
noncomputable def verticalDirectionsOutside (label : W → G)
    (L : Finset (VertexIndex G)) (v : VertexIndex G) : Finset W := by
  classical
  exact Finset.univ.filter fun b => verticalNeighbor label v b ∉ L
noncomputable def activeFaceDirectionPairs (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) (A B : Finset W) : Finset (W × W) := by
  classical
  exact (A ×ˢ B).filter fun p => localFaceMatrix label c v p.2 p.1 ≠ 0
noncomputable def edgeExpandingVertices (label : W → G)
    (L : Finset (VertexIndex G)) (m : Nat) : Finset (VertexIndex G) := by
  classical
  exact L.filter fun v => m ≤ ∑ u ∈ L, adjacencyGraph label v u
noncomputable def faceExpandingVertices (label : W → G)
    (L : Finset (VertexIndex G)) (s : Nat) : Finset (VertexIndex G) := by
  classical
  exact L.filter fun v => s ≤ ∑ u ∈ L, faceSquareGraph label v u
def CarriesActiveFaceVerticalEdgeAt (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) (b : W) : Prop :=
  ∃ a, localFaceMatrix label c v b a ≠ 0
def IsFaceActiveVerticalEdgeAt (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) (b : W) : Prop :=
  CarriesActiveFaceVerticalEdgeAt label c v b ∧
    v ∉ vertexBlockSupport c ∧
      verticalNeighbor label v b ∉ vertexBlockSupport c
def IsIncidentToFaceActiveVerticalEdge (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) : Prop :=
  ∃ b, IsFaceActiveVerticalEdgeAt label c v b
def IsClosedLabelledSet (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (m : Nat) (L : Finset (VertexIndex G)) : Prop :=
  vertexBlockSupport c ⊆ L ∧
    ∀ v, IsIncidentToFaceActiveVerticalEdge label c v →
      m ≤ ∑ u ∈ L, adjacencyGraph label v u → v ∈ L
noncomputable def labelledVertices (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (m : Nat) : Finset (VertexIndex G) := by
  classical
  exact Finset.univ.filter fun v =>
    ∀ L, IsClosedLabelledSet label c m L → v ∈ L
end QEC.Coding.TannerLiftedProduct


