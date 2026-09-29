-- Prove2me | Definitions.Def_PolygonalArcTerminalEndpointCone
-- name    : PolygonalArcTerminalEndpointCone
-- status  : Definition
-- author  : @xuanji
-- created : 2026-09-27T23:44:04.270154+00:00
-- url     : https://prove2.me/theorems/fa556419-95d4-46ca-bdfe-e669917cd683
-- title:
--   PolygonalArcTerminalEndpointCone
-- statement:
--   The open two-sided cone at the terminal endpoint of a polygonal arc, expressed in coordinates determined by the final edge and its quarter-turn normal.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcTerminalEndpointCone.lean#L1-23

import Definitions.Def_PlanarRot90
import Definitions.Def_PolygonalArc

open Classical
noncomputable section

-- [TABLET NODE: PolygonalArcTerminalEndpointCone]
-- Source: https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcTerminalEndpointCone.lean#L1-23
def PolygonalArcTerminalEndpointCone (γ : PolygonalArc) (r K : ℝ) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  let hprev : γ.vertices.length - 2 < γ.vertices.length := by
    have hlen := γ.length_ge_two
    omega
  let p0 : EuclideanSpace ℝ (Fin 2) := γ.target
  let p1 : EuclideanSpace ℝ (Fin 2) := γ.vertices[γ.vertices.length - 2]'hprev
  let d : EuclideanSpace ℝ (Fin 2) := p1 - p0
  let chart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    fun z => p0 + z 0 • d + z 1 • PlanarRot90 d
  let a : ℝ := r / dist p0 p1
  chart ''
    {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ -K * z 0 < z 1 ∧
      z 1 < K * z 0}


