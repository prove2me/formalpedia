-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAffineCompletionNormal
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAffineCompletionNormal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:02.874251+00:00
-- url     : https://prove2.me/theorems/e522da2c-bb1d-489e-b1f9-eb9ff952cb5e
-- title:
--   St Affine Completion Normal
-- statement:
--   Definitions and structural lemmas for St Affine Completion Normal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StAffineCompletionNormal.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZariskiObjects
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
def AffineCompletionNormal.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (m : Ideal (MvPolynomial σ ℂ ⧸ I)),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → m.IsMaximal →
      IsDomain (AdicCompletion m (MvPolynomial σ ℂ ⧸ I)) ∧
        IsIntegrallyClosed (AdicCompletion m (MvPolynomial σ ℂ ⧸ I))
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


