-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelProjectionLocallyInjective
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelProjectionLocallyInjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:58.989732+00:00
-- url     : https://prove2.me/theorems/feec8fd8-5a81-4225-b630-b5a9b0437286
-- title:
--   St Normal Model Projection Locally Injective
-- statement:
--   Definitions and structural lemmas for St Normal Model Projection Locally Injective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StNormalModelProjectionLocallyInjective.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalCurveBranchOrder
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
open MvPolynomial Topology
noncomputable section
def NormalModelProjectionLocallyInjective.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (w : Fin n ⊕ Fin M.m → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ) → w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal →
      ∃ U ∈ 𝓝 w, Set.InjOn IndefiniteRowSideFullHecke.ComplexSets.firstCoords (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∩ U)
end
end GroundTheory.Heights₂.Heights


