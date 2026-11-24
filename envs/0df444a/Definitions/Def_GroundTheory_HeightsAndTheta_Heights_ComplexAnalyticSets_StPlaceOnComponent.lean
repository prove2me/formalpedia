-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPlaceOnComponent
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPlaceOnComponent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:05.615026+00:00
-- url     : https://prove2.me/theorems/7e7c6747-c162-4c1c-a370-97005d31f949
-- title:
--   St Place On Component
-- statement:
--   Definitions and structural lemmas for St Place On Component, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StPlaceOnComponent.lean

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
def PlaceOnComponent.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 →
      ∀ P : MaximalSpectrum (curveNormalisation I q), ∃ J : Ideal (MvPolynomial (Fin n) ℂ),
        J ∈ I.minimalPrimes ∧ J ≤ RingHom.ker (eval q) ∧ ringKrullDim (curveLocalRing J q) = 1 ∧
        ∃ P' : MaximalSpectrum (curveNormalisation J q), ∀ f : MvPolynomial (Fin n) ℂ,
          Ring.ord (Localization.AtPrime P.asIdeal)
            (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
              (algebraMap (curveLocalRing I q) (curveNormalisation I q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) =
          Ring.ord (Localization.AtPrime P'.asIdeal)
            (algebraMap (curveNormalisation J q) (Localization.AtPrime P'.asIdeal)
              (algebraMap (curveLocalRing J q) (curveNormalisation J q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q) f)))
end
end GroundTheory.Heights₂.Heights


