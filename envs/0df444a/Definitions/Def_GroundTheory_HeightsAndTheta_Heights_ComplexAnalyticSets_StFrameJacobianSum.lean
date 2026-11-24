-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFrameJacobianSum
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFrameJacobianSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:43:41.308801+00:00
-- url     : https://prove2.me/theorems/409053a1-75d1-4ccc-97de-995e768c7949
-- title:
--   St Frame Jacobian Sum
-- statement:
--   Definitions and structural lemmas for St Frame Jacobian Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StFrameJacobianSum.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
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
open Module
noncomputable section
def frameProjLin {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ I :=
  (WithLp.linearEquiv 2 ℂ (I → ℂ)).symm.toLinearMap ∘ₗ LinearMap.pi fun i : I => innerₛₗ ℂ (b i)
def FrameJacobianSum.Statement : Prop :=
  ∀ (d n : ℕ) (T : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))),
    areaJacobian (T.restrictScalars ℝ) =
      ∑ I ∈ Finset.univ.powersetCard d, areaJacobian ((frameProjLin b I ∘ₗ T).restrictScalars ℝ)
end
end GroundTheory.Heights₂.Heights


