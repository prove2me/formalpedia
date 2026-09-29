-- Prove2me | Definitions.Def_PolygonalArcCollarControlRadii
-- name    : PolygonalArcCollarControlRadii
-- status  : Definition
-- author  : @xuanji
-- created : 2026-09-27T22:45:53.773799+00:00
-- url     : https://prove2.me/theorems/0cf338b1-25b5-4444-b0d4-0e780c4eef96
-- title:
--   Collar-control radii for a polygonal arc
-- statement:
--   For a polygonal arc and a positive tolerance, this structure records a positive radius at every vertex. The radii are smaller than the tolerance, the corresponding closed vertex balls are pairwise disjoint, adjacent radii have sum smaller than the adjacent edge length, and every vertex ball is disjoint from every nonincident edge. These data provide uniform local control around all vertices of the arc.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcCollarControlRadii.lean#L1-L22

import Definitions.Def_PolygonalArc

-- [TABLET NODE: PolygonalArcCollarControlRadii]
-- Source: https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcCollarControlRadii.lean#L1-L22
structure PolygonalArcCollarControlRadii (γ : PolygonalArc) (η : ℝ) where
  radius : Fin γ.vertices.length → ℝ
  radius_pos : ∀ i, 0 < radius i
  radius_lt_eta : ∀ i, radius i < η
  control_disks_disjoint :
    ∀ ⦃i j : Fin γ.vertices.length⦄, i ≠ j →
      Disjoint (Metric.closedBall γ.vertices[i.1] (radius i))
        (Metric.closedBall γ.vertices[j.1] (radius j))
  adjacent_radii_sum_lt :
    ∀ ⦃j : ℕ⦄, (hj : j + 1 < γ.vertices.length) →
      radius ⟨j, Nat.lt_of_succ_lt hj⟩ + radius ⟨j + 1, hj⟩ <
        dist γ.vertices[j] γ.vertices[j + 1]
  nonincident_segment_disjoint :
    ∀ ⦃i : Fin γ.vertices.length⦄ ⦃j : ℕ⦄,
      (hj : j + 1 < γ.vertices.length) →
        i.1 ≠ j → i.1 ≠ j + 1 →
          Disjoint (Metric.closedBall γ.vertices[i.1] (radius i))
            (segment ℝ γ.vertices[j] γ.vertices[j + 1])


