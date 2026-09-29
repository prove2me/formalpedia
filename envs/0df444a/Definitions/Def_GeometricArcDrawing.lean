-- Prove2me | Definitions.Def_GeometricArcDrawing
-- name    : GeometricArcDrawing
-- status  : Definition
-- author  : @xuanji
-- created : 2026-09-26T20:21:13.866389+00:00
-- url     : https://prove2.me/theorems/c711f45a-4461-47e6-8775-76c17b4b4106
-- title:
--   Geometric arc drawing
-- statement:
--   A geometric arc drawing assigns an injective placement in the Euclidean plane to the vertices of a finite simple graph and assigns each edge a carrier and relative interior. Each edge is required to be either a nondegenerate straight line segment or an injective continuous circular arc joining the placements of its endpoints. Vertices may not lie in edge interiors, and distinct edges may not share a nondegenerate subarc. The structure also records the finite set of pairwise interior intersection points and the local pair count obtained by summing, at each intersection point, the number of unordered pairs of incident edge branches.
--
--   This is the geometric input used to replace circular or straight geometric arcs by ordinary polygonal arcs while controlling the resulting crossing count.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/GeometricArcDrawing.lean#L1-L63

-- Preamble: shared imports for all tablet nodes.
-- Add specific Mathlib imports here (never `import Mathlib`).
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

open Classical
noncomputable section

-- [TABLET NODE: GeometricArcDrawing]
structure GeometricArcDrawing {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] where
-- BODY
  vertexPlacement : V → EuclideanSpace ℝ (Fin 2)
  vertexPlacement_injective : Function.Injective vertexPlacement
  edgeSource : G.edgeFinset → EuclideanSpace ℝ (Fin 2)
  edgeTarget : G.edgeFinset → EuclideanSpace ℝ (Fin 2)
  edgeCarrier : G.edgeFinset → Set (EuclideanSpace ℝ (Fin 2))
  edgeRelativeInterior : G.edgeFinset → Set (EuclideanSpace ℝ (Fin 2))
  edgeArc_endpoints :
    ∀ e : G.edgeFinset,
      ∃ u v : V,
        G.Adj u v ∧ e.1 = Sym2.mk u v ∧
          (((edgeSource e = vertexPlacement u ∧
              edgeTarget e = vertexPlacement v) ∨
            (edgeSource e = vertexPlacement v ∧
              edgeTarget e = vertexPlacement u)))
  edge_is_simple_lineSegment_or_circularArc :
    ∀ e : G.edgeFinset,
      ((edgeSource e ≠ edgeTarget e) ∧
        edgeCarrier e = segment ℝ (edgeSource e) (edgeTarget e) ∧
        edgeRelativeInterior e = openSegment ℝ (edgeSource e) (edgeTarget e)) ∨
      (∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
          (γ : Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2)),
        0 < r ∧
          Continuous γ ∧ Function.Injective γ ∧
          (∀ t, dist (γ t) c = r) ∧
          γ ⟨0, by simp⟩ = edgeSource e ∧
          γ ⟨1, by simp⟩ = edgeTarget e ∧
          edgeCarrier e = Set.range γ ∧
          edgeRelativeInterior e =
            Set.range (fun t : {t : ℝ // 0 < t ∧ t < 1} =>
              γ ⟨t.1, ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩))
  no_vertex_in_edge_interior :
    ∀ (v : V) (e : G.edgeFinset),
      vertexPlacement v ∉ edgeRelativeInterior e
  no_shared_nondegenerate_subarc :
    ∀ ⦃e₁ e₂ : G.edgeFinset⦄,
      e₁ ≠ e₂ →
        ¬ ∃ γ : Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2),
          Continuous γ ∧ Function.Injective γ ∧
            γ ⟨0, by simp⟩ ≠ γ ⟨1, by simp⟩ ∧
              Set.range γ ⊆ edgeCarrier e₁ ∩ edgeCarrier e₂
  intersectionPoints : Finset (EuclideanSpace ℝ (Fin 2))
  intersectionPoints_spec :
    ∀ p : EuclideanSpace ℝ (Fin 2),
      p ∈ intersectionPoints ↔
        ∃ e₁ e₂ : G.edgeFinset,
          e₁ ≠ e₂ ∧
            p ∈ edgeRelativeInterior e₁ ∧
              p ∈ edgeRelativeInterior e₂
  localPairCount : ℕ
  localPairCount_eq :
    localPairCount =
      intersectionPoints.sum (fun p =>
        Nat.choose (((Finset.univ : Finset G.edgeFinset).filter
          (fun e => p ∈ edgeRelativeInterior e)).card) 2)


