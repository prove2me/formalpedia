-- Prove2me | Definitions.Def_PolygonalArcInitialEndpointLeftCone
-- name    : PolygonalArcInitialEndpointLeftCone
-- status  : Definition
-- author  : @xuanji
-- created : 2026-09-27T21:37:20.770524+00:00
-- url     : https://prove2.me/theorems/30de0358-424b-40e2-93c4-344164aa9c1f
-- title:
--   Initial endpoint left cone
-- statement:
--   The local left-hand cone at the initial endpoint of a polygonal arc, expressed in coordinates determined by the first edge and its quarter-turn normal.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcInitialEndpointLeftCone.lean

import Mathlib.Tactic
import Definitions.Def_PlanarRot90
import Definitions.Def_PolygonalArc

open Classical
noncomputable section

-- [TABLET NODE: PolygonalArcInitialEndpointLeftCone]
-- Source: https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcInitialEndpointLeftCone.lean#L1-L20
def PolygonalArcInitialEndpointLeftCone (γ : PolygonalArc) (r K : ℝ) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  let hfirst : 1 < γ.vertices.length := Nat.lt_of_succ_le γ.length_ge_two
  let p0 : EuclideanSpace ℝ (Fin 2) := γ.source
  let p1 : EuclideanSpace ℝ (Fin 2) := γ.vertices[1]'hfirst
  let d : EuclideanSpace ℝ (Fin 2) := p1 - p0
  let chart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    fun z => p0 + z 0 • d + z 1 • PlanarRot90 d
  let a : ℝ := r / dist p0 p1
  chart ''
    {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ 0 < z 1 ∧
      z 1 < K * z 0}


