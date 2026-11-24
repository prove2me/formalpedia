-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveCoordinateGraph
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveCoordinateGraph
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:42.956389+00:00
-- url     : https://prove2.me/theorems/06e9c790-04a5-45c5-8643-3cb8fa1cd453
-- title:
--   St Curve Coordinate Graph
-- statement:
--   Definitions and structural lemmas for St Curve Coordinate Graph, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StCurveCoordinateGraph.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchNormalisation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial ComplexSets Filter Topology
noncomputable section
def IsCoordinateGraphNear {n : ℕ} (X : Set (Fin n → ℂ)) (x : Fin n → ℂ) : Prop :=
  x ∈ X ∧ ∃ W : Set (Fin n → ℂ), IsOpen W ∧ x ∈ W ∧ ∃ (i : Fin n) (V : Set ℂ) (g : ℂ → Fin n → ℂ),
    IsOpen V ∧ DifferentiableOn ℂ g V ∧ (∀ t ∈ V, g t i = t) ∧ ∀ z ∈ W, z ∈ X ↔ (z i ∈ V ∧ g (z i) = z)
def CurveCoordinateGraph.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 →
    ∃ ε > 0, ∀ x ∈ zeroSet I, x ∈ Metric.ball q ε → x ≠ q → IsCoordinateGraphNear (zeroSet I) x
end
end GroundTheory.Heights₂.Heights


