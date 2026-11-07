-- Prove2me | Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleGeometry
-- name    : QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleGeometry
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:07:54.675362+00:00
-- url     : https://prove2.me/theorems/5cdeec2d-7232-400f-a9a9-c0551a1de7b7
-- title:
--   Triangle Geometry
-- statement:
--   Definitions and structural lemmas for Triangle Geometry, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/TriangleGeometry.lean

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Measure
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.Maps.Proper.Basic
set_option autoImplicit false
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set
open scoped BigOperators
noncomputable def barycenterMap (a : Fin 3 → Space) : (Fin 3 → ℝ) →ₗ[ℝ] Space :=
  ∑ i, (LinearMap.proj i).smulRight (a i)
def triangleHit (r : Fin 3 → Space) (z : Space) (ρ : ℝ) : Set (Fin 3 → Space) :=
  {p | ∃ y ∈ convexHull ℝ (range fun j => r j+p j), dist y z ≤ ρ}
def largeWeightHit (r : Fin 3 → Space) (z : Space) (ρ : ℝ) (i : Fin 3) :
    Set (Fin 3 → Space) :=
  {p | ∃ w : stdSimplex ℝ (Fin 3), (1:ℝ)/3 ≤ (w : Fin 3 → ℝ) i ∧
    dist (∑ j, (w : Fin 3 → ℝ) j • (r j + p j)) z ≤ ρ}
end QEC.Coding.ProbabilisticConstruction.SphericalCap


