-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryBound
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:46:49.2918+00:00
-- url     : https://prove2.me/theorems/3dc67509-09f6-45da-a8d6-fbe06a86dc10
-- title:
--   St Cut Off Boundary Bound
-- statement:
--   Definitions and structural lemmas for St Cut Off Boundary Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StCutOffBoundaryBound.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
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
open MvPolynomial MeasureTheory Matrix ComplexSets
open scoped ContDiff
noncomputable section
def CutOffBoundaryBound.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (F G : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    SmoothNear (zeroSet J) F → SmoothNear (zeroSet J) G → (∀ i, SmoothNear (zeroSet J) (φ i)) →
    HasCompactSupport F →
      ∃ R C : ℝ, ∀ χ : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ χ →
        |chartInt J A G (vecCons (fun x => χ x * F x) φ) -
            chartInt J A (fun x => χ x * G x) (vecCons F φ)| ≤
          C * ((∫ y, chartAbsDens J A ((Metric.closedBall 0 R).indicator fun _ => 1) (vecCons χ φ) y) +
            Real.sqrt (energyInt J A (Metric.closedBall 0 R) χ))
end
end GroundTheory.Heights₂.Heights


