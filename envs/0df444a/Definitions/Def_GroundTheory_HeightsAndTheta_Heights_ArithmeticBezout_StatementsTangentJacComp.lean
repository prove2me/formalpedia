-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentJacComp
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentJacComp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:52.844042+00:00
-- url     : https://prove2.me/theorems/bf9b59a7-78d4-4095-a296-dca0f918206b
-- title:
--   Statements Tangent Jac Comp
-- statement:
--   Definitions and structural lemmas for Statements Tangent Jac Comp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsTangentJacComp.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeTangentAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaMultiplicity
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
noncomputable section
def TangentJacComp.Statement : Prop :=
  ∀ (d n : ℕ) (L : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) (π : Fin d → Fin n → ℂ),
    tangentJac π (LinearMap.range L) * areaJacobian (L.restrictScalars ℝ) =
      |LinearMap.det (((linProjₗ π).comp L).restrictScalars ℝ)|
end
end GroundTheory.Heights₂.Heights


