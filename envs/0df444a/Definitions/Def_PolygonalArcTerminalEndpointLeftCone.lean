-- Prove2me | Definitions.Def_PolygonalArcTerminalEndpointLeftCone
-- name    : PolygonalArcTerminalEndpointLeftCone
-- status  : Definition
-- author  : @xuanji
-- created : 2026-09-27T21:37:32.266034+00:00
-- url     : https://prove2.me/theorems/eb9052ab-db53-44cb-b476-05c6f73824b2
-- title:
--   Terminal endpoint left cone
-- statement:
--   The local left-hand cone at the terminal endpoint of a polygonal arc, expressed in coordinates determined by the final edge and its quarter-turn normal.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcTerminalEndpointLeftCone.lean

import Mathlib.Tactic
import Definitions.Def_PlanarRot90
import Definitions.Def_PolygonalArc

open Classical
noncomputable section

-- [TABLET NODE: PolygonalArcTerminalEndpointLeftCone]
-- Source: https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcTerminalEndpointLeftCone.lean#L1-L20
def PolygonalArcTerminalEndpointLeftCone (γ : PolygonalArc) (r K : ℝ) :
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
      z 1 < 0}


