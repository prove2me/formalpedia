-- Prove2me | Definitions.Def_wdw_canonical_geometry
-- name    : wdw_canonical_geometry
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-10-03T20:53:58.616988+00:00
-- url     : https://prove2.me/theorems/c474a433-ea35-46d9-8e45-7b3132934926
-- title:
--   Spatial metric coefficients and the DeWitt metric
-- statement:
--   Coordinate coefficient interface on arbitrary configuration and spatial types: a positive definite real three-metric with positive determinant, its positive square-root volume density, and the DeWitt coefficient of equation (5). Scalar curvature is supplied data, not derived from a connection. No smooth manifold or chart-compatibility property is encoded.
-- source:
--   Claus Kiefer, Quantum Geometrodynamics: whence, whither?, Gen. Relativ. Gravit. 41 (2009), 877–901, https://arxiv.org/abs/0812.0295, Sections 2.2 and 2.4, equations (3)–(8). Formal algebraic derivation with supplied geometry and complex-linear derivative interface; no analytic realization asserted.

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Complex.Basic

set_option autoImplicit false

namespace WheelerDeWitt

noncomputable section

/-- Coordinate coefficient data for the formal canonical constraint.
`scalarCurvature` is supplied geometric data, not a construction of Ricci curvature. -/
structure Geometry (C X : Type*) where
  metric : C → X → Matrix (Fin 3) (Fin 3) ℝ
  metric_posDef : ∀ q x, (metric q x).PosDef
  determinant_pos : ∀ q x, 0 < (metric q x).det
  scalarCurvature : C → X → ℝ

def volumeDensity {C X : Type*} (g : Geometry C X) (q : C) (x : X) : ℝ :=
  Real.sqrt (g.metric q x).det

def deWittMetric {C X : Type*} (g : Geometry C X) (q : C) (x : X)
    (a b c d : Fin 3) : ℝ :=
  (g.metric q x a c * g.metric q x b d +
   g.metric q x a d * g.metric q x b c -
   g.metric q x a b * g.metric q x c d) / (2 * volumeDensity g q x)

end
end WheelerDeWitt


