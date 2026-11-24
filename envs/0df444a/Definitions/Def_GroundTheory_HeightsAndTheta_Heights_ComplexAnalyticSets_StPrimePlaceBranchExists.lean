-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimePlaceBranchExists
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimePlaceBranchExists
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:29.496258+00:00
-- url     : https://prove2.me/theorems/a62b6998-c570-4559-94ef-25be910aeaf5
-- title:
--   St Prime Place Branch Exists
-- statement:
--   Definitions and structural lemmas for St Prime Place Branch Exists, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StPrimePlaceBranchExists.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchNormalisation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveResidueDegree
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
open MvPolynomial ComplexSets
noncomputable section
def PrimePlaceBranchExists.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ),
    J.IsPrime → ringKrullDim (curveLocalRing J q) = 1 →
      ∀ P : MaximalSpectrum (curveNormalisation J q), ∃ ν : VarBranch J 1 q, ∀ f : MvPolynomial (Fin n) ℂ,
        Ring.ord (Localization.AtPrime P.asIdeal)
            (algebraMap (curveNormalisation J q) (Localization.AtPrime P.asIdeal)
              (algebraMap (curveLocalRing J q) (curveNormalisation J q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q) f))) = branchOrder ν f
end
end GroundTheory.Heights₂.Heights


