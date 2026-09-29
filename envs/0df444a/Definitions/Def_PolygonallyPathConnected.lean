-- Prove2me | Definitions.Def_PolygonallyPathConnected
-- name    : PolygonallyPathConnected
-- status  : Definition
-- author  : @xuanji
-- created : 2026-09-26T22:20:54.734469+00:00
-- url     : https://prove2.me/theorems/9f7dcc8e-099e-4670-8786-76b4e2622429
-- title:
--   Polygonal path connectedness
-- statement:
--   A subset of the plane is polygonally path connected when every pair of its points can be joined by a polygonal path whose source and target are those points and whose entire carrier remains inside the subset. This predicate is the connectivity interface used for complements of planar drawings.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonallyPathConnected.lean#L1-L9

import Definitions.Def_PolygonalPath

-- [TABLET NODE: PolygonallyPathConnected]
def PolygonallyPathConnected (S : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
-- BODY
  ∀ ⦃p q : EuclideanSpace ℝ (Fin 2)⦄,
    p ∈ S → q ∈ S →
      ∃ γ : PolygonalPath,
        γ.source = p ∧ γ.target = q ∧ γ.carrier ⊆ S


