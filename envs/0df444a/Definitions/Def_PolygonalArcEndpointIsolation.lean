-- Prove2me | Definitions.Def_PolygonalArcEndpointIsolation
-- name    : PolygonalArcEndpointIsolation
-- status  : Definition
-- author  : @xuanji
-- created : 2026-09-27T21:36:05.613044+00:00
-- url     : https://prove2.me/theorems/2d75d8ae-b55d-4e16-93ae-acb9cf194359
-- title:
--   Endpoint isolation radii for a polygonal arc
-- statement:
--   A pair of positive endpoint radii that are shorter than the incident endpoint edges, whose closed balls are disjoint and whose intersections with the arc lie on the corresponding endpoint segments.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcEndpointIsolation.lean

import Mathlib.Tactic
import Definitions.Def_PolygonalArc
import Definitions.Def_PolygonalArcInitialEndpointSegmentLength
import Definitions.Def_PolygonalArcTerminalEndpointSegmentLength

open Classical
noncomputable section

-- [TABLET NODE: PolygonalArcEndpointIsolation]
-- Source: https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcEndpointIsolation.lean#L1-L27
structure PolygonalArcEndpointIsolation (γ : PolygonalArc) (r₀ r₁ : ℝ) : Prop where
  source_pos : 0 < r₀
  target_pos : 0 < r₁
  source_lt_initial_length : r₀ < PolygonalArcInitialEndpointSegmentLength γ
  target_lt_terminal_length : r₁ < PolygonalArcTerminalEndpointSegmentLength γ
  endpoint_closedBalls_disjoint :
    Disjoint (Metric.closedBall γ.source r₀) (Metric.closedBall γ.target r₁)
  source_closedBall_carrier_subset_initial_segment :
    let hfirst : 1 < γ.vertices.length := Nat.lt_of_succ_le γ.length_ge_two
    Metric.closedBall γ.source r₀ ∩ γ.carrier ⊆
      segment ℝ γ.source (γ.vertices[1]'hfirst)
  target_closedBall_carrier_subset_terminal_segment :
    let hprev : γ.vertices.length - 2 < γ.vertices.length := by
      have hlen := γ.length_ge_two
      omega
    Metric.closedBall γ.target r₁ ∩ γ.carrier ⊆
      segment ℝ γ.target (γ.vertices[γ.vertices.length - 2]'hprev)


