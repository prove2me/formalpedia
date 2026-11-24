-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSmoothLocalGraph
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSmoothLocalGraph
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:02.455894+00:00
-- url     : https://prove2.me/theorems/cccddb7a-9667-4a13-bc9b-053144164736
-- title:
--   PCone Smooth Local Graph
-- statement:
--   Definitions and structural lemmas for PCone Smooth Local Graph, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSmoothLocalGraph.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSmoothLocalGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPolyLocalGenerators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsHolomorphicImplicitGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLocalMass
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
open MvPolynomial Module
noncomputable section
variable {n : ℕ}
def HermNorm.pointOfE (h : HermNorm n) : EuclideanSpace ℂ (Fin n) ≃ₗ[ℂ] (Fin n → ℂ) :=
  h.pointOfL.toLinearEquiv.trans (WithLp.linearEquiv 2 ℂ (Fin n → ℂ))
def HermNorm.pointOfC (h : HermNorm n) : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap (h.pointOfE : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] (Fin n → ℂ))
end
end GroundTheory.Heights₂.Heights


