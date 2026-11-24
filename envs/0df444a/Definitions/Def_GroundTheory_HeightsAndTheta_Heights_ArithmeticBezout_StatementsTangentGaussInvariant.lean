-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentGaussInvariant
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentGaussInvariant
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:00:27.172472+00:00
-- url     : https://prove2.me/theorems/15ef70a6-9ee8-4dbf-9d4b-c44000e47444
-- title:
--   Statements Tangent Gauss Invariant
-- statement:
--   Definitions and structural lemmas for Statements Tangent Gauss Invariant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsTangentGaussInvariant.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeTangentAverage
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
open MvPolynomial MeasureTheory Module
open scoped ENNReal
noncomputable section
def TangentGaussInvariant.Statement : Prop :=
  ∀ (n m : ℕ), 0 < m → m ≤ n → ∀ T : Submodule ℂ (EuclideanSpace ℂ (Fin n)), finrank ℂ T = m →
    ∀ y ∈ T,
      ∫⁻ π : Fin m → Fin n → ℂ, matGauss π *
          (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) *
            ENNReal.ofReal (tangentJac π T) =
        tangentGaussProfile n m ‖y‖
end
end GroundTheory.Heights₂.Heights


