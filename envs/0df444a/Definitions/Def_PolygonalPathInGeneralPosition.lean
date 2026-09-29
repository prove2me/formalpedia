-- Prove2me | Definitions.Def_PolygonalPathInGeneralPosition
-- name    : PolygonalPathInGeneralPosition
-- status  : Definition
-- author  : @xuanji
-- created : 2026-09-27T19:55:35.767286+00:00
-- url     : https://prove2.me/theorems/40108a7c-600c-4d42-801f-8b948f46049b
-- title:
--   Polygonal path in general position
-- statement:
--   A polygonal path is in general position with respect to a finite polygonal set when its vertices avoid the set's carrier, its marked points avoid the path carrier, no path segment shares a nontrivial segment with a listed segment of the finite set, and any interior intersection of two segments is transverse rather than collinear. Finally, the path carrier meets the finite-set carrier in only finitely many points. This predicate records the controlled-intersection hypothesis used by perturbation and crossing-elimination arguments.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalPathInGeneralPosition.lean#L1-L25

import Definitions.Def_PolygonalPath
import Definitions.Def_FinitePolygonalSet

open Classical
noncomputable section

-- [TABLET NODE: PolygonalPathInGeneralPosition]
def PolygonalPathInGeneralPosition (γ : PolygonalPath) (K : FinitePolygonalSet) : Prop :=
  (∀ v : EuclideanSpace ℝ (Fin 2), v ∈ γ.vertices → v ∉ K.carrier) ∧
    (∀ p : EuclideanSpace ℝ (Fin 2), p ∈ K.points → p ∉ γ.carrier) ∧
      (∀ (i : ℕ) (hi : i + 1 < γ.vertices.length)
          (s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)),
          s ∈ K.segments →
            ¬ ∃ p q : EuclideanSpace ℝ (Fin 2),
              p ≠ q ∧
                segment ℝ p q ⊆
                  segment ℝ γ.vertices[i] γ.vertices[i + 1] ∩ segment ℝ s.1 s.2) ∧
        (∀ (i : ℕ) (hi : i + 1 < γ.vertices.length)
            (s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))
            (hs : s ∈ K.segments) (p : EuclideanSpace ℝ (Fin 2)),
            p ∈ openSegment ℝ γ.vertices[i] γ.vertices[i + 1] →
              p ∈ openSegment ℝ s.1 s.2 →
                ¬ ∃ c : ℝ, s.2 - s.1 = c • (γ.vertices[i + 1] - γ.vertices[i])) ∧
          Set.Finite (γ.carrier ∩ K.carrier)


