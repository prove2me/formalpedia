-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentJacCompress
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentJacCompress
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:31:51.633332+00:00
-- url     : https://prove2.me/theorems/b3bdb01a-bf1a-4b29-b816-06ba7a062bc9
-- title:
--   Statements Tangent Jac Compress
-- statement:
--   Definitions and structural lemmas for Statements Tangent Jac Compress, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsTangentJacCompress.lean

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
open MeasureTheory Module
noncomputable section
def TangentJacCompress.Statement : Prop :=
  ∀ (n m : ℕ) (π : Fin m → Fin n → ℂ) (T : Submodule ℂ (EuclideanSpace ℂ (Fin n))),
    ((tangentJac π T : ℝ) : ℂ) =
      (T.starProjection ∘L (LinearMap.toContinuousLinearMap (linProjₗ π)).adjoint ∘L
          LinearMap.toContinuousLinearMap (linProjₗ π) ∘L T.starProjection +
        (1 - T.starProjection)).det
end
end GroundTheory.Heights₂.Heights


