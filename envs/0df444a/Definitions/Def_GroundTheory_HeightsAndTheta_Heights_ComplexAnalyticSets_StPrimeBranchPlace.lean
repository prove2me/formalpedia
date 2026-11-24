-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeBranchPlace
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeBranchPlace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:12.206844+00:00
-- url     : https://prove2.me/theorems/bc9f8d3c-6120-44fd-9e5b-2d824adf179c
-- title:
--   St Prime Branch Place
-- statement:
--   Definitions and structural lemmas for St Prime Branch Place, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StPrimeBranchPlace.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchNormalisation
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
def PrimeBranchPlace.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (c : VarBranch J 1 q),
    J.IsPrime → ringKrullDim (curveLocalRing J q) ≤ 1 →
      ∃ P : MaximalSpectrum (curveNormalisation J q), ∀ f : MvPolynomial (Fin n) ℂ,
        Ring.ord (Localization.AtPrime P.asIdeal)
            (algebraMap (curveNormalisation J q) (Localization.AtPrime P.asIdeal)
              (algebraMap (curveLocalRing J q) (curveNormalisation J q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q) f))) = branchOrder c f
end
end GroundTheory.Heights₂.Heights


