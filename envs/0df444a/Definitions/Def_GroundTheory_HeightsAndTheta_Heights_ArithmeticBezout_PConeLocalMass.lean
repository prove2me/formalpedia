-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLocalMass
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLocalMass
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:38:42.72955+00:00
-- url     : https://prove2.me/theorems/a34910cd-1634-450e-9e98-9a0d91ee4bb4
-- title:
--   PCone Local Mass
-- statement:
--   Definitions and structural lemmas for PCone Local Mass, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeLocalMass.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeLocalMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFiniteFibreDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralLine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_pointOf_eq_zero_1a71672ffe50

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
open MvPolynomial MeasureTheory
open scoped ENNReal NNReal
noncomputable section
variable {n : ℕ}
def HermNorm.pointOfₗ (h : HermNorm n) :
    EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) where
  toFun y := WithLp.toLp 2 (h.pointOf y)
  map_add' v w := by rw [HermNorm.pointOf_add']; rfl
  map_smul' c v := by rw [HermNorm.pointOf_smul']; rfl
theorem HermNorm.pointOfₗ_injective (h : HermNorm n) : Function.Injective h.pointOfₗ := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  apply h.pointOf_eq_zero
  have := congrArg WithLp.ofLp hy
  simpa [HermNorm.pointOfₗ] using this
def HermNorm.pointOfL (h : HermNorm n) : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n) :=
  (LinearEquiv.ofInjectiveEndo h.pointOfₗ h.pointOfₗ_injective).toContinuousLinearEquiv
end
end GroundTheory.Heights₂.Heights


