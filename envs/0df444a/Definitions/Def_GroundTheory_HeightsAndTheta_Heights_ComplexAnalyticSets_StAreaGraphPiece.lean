-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaGraphPiece
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaGraphPiece
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:03.659802+00:00
-- url     : https://prove2.me/theorems/7b0dc449-50ec-43c5-94ad-33030700889c
-- title:
--   St Area Graph Piece
-- statement:
--   Definitions and structural lemmas for St Area Graph Piece, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StAreaGraphPiece.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGraphJacContinuous
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
open MeasureTheory
open scoped ENNReal NNReal
noncomputable section
def AreaGraphPiece.Statement : Prop :=
  ∀ (k m : ℕ) (F : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m))
    (A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)) (δ : ℝ≥0)
    (t : Set (EuclideanSpace ℝ (Fin k))), δ < 1 → ApproximatesLinearOn F A t δ →
      μH[(k : ℝ)] (realGraphPt F '' t) ≤
          ((1 + δ : ℝ≥0) : ℝ≥0∞) ^ k *
            ENNReal.ofReal (graphJac (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) *
              μH[(k : ℝ)] t ∧
        ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ k *
            ENNReal.ofReal (graphJac (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) *
              μH[(k : ℝ)] t ≤
          μH[(k : ℝ)] (realGraphPt F '' t)
end
end GroundTheory.Heights₂.Heights


