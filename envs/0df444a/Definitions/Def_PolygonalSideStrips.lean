-- Prove2me | Definitions.Def_PolygonalSideStrips
-- name    : PolygonalSideStrips
-- status  : Definition
-- author  : @xuanji
-- created : 2026-09-27T21:36:54.148986+00:00
-- url     : https://prove2.me/theorems/8e67ef34-8985-4990-b439-b359c56db913
-- title:
--   Polygonal side-strip data
-- statement:
--   A collar together with left and right open connected side strips around a polygonal arc. The strips are disjoint from the arc and from each other, cover the collar away from the relative interior, and have the relative interior in each strip closure.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalSideStrips.lean

import Definitions.Def_PolygonalArc

-- [TABLET NODE: PolygonalSideStrips]
-- Source: https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalSideStrips.lean#L1-L25
structure PolygonalSideStrips (γ : PolygonalArc) where
  collar : Set (EuclideanSpace ℝ (Fin 2))
  leftStrip : Set (EuclideanSpace ℝ (Fin 2))
  rightStrip : Set (EuclideanSpace ℝ (Fin 2))
  collar_open : IsOpen collar
  left_open : IsOpen leftStrip
  right_open : IsOpen rightStrip
  relativeInterior_subset_collar : γ.relativeInterior ⊆ collar
  left_subset_collar : leftStrip ⊆ collar
  right_subset_collar : rightStrip ⊆ collar
  left_connected : IsConnected leftStrip
  right_connected : IsConnected rightStrip
  left_disjoint_arc : Disjoint leftStrip γ.carrier
  right_disjoint_arc : Disjoint rightStrip γ.carrier
  side_strips_disjoint : Disjoint leftStrip rightStrip
  relativeInterior_subset_closure_left :
    γ.relativeInterior ⊆ closure leftStrip
  relativeInterior_subset_closure_right :
    γ.relativeInterior ⊆ closure rightStrip
  collar_without_arc :
    collar \ γ.relativeInterior = leftStrip ∪ rightStrip


