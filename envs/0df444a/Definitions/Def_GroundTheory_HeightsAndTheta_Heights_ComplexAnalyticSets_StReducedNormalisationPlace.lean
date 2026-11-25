-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StReducedNormalisationPlace
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StReducedNormalisationPlace
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T07:08:24.739813+00:00
-- url     : https://prove2.me/theorems/e2d0049b-2952-43a7-9fd8-d27c2bcb9d07
-- title:
--   St Reduced Normalisation Place
-- statement:
--   Definitions and structural lemmas for St Reduced Normalisation Place, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StReducedNormalisationPlace.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveResidueDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CurveNormalisationFiniteLemmas
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
def ReducedNormalisationPlace.Statement : Prop :=
  ∀ (R : Type) [CommRing R] [IsReduced R] [IsNoetherianRing R]
    (P : MaximalSpectrum (integralClosure R (FractionRing R))),
    ∃ p ∈ minimalPrimes R, ∀ (S : Type) [CommRing S] (φ : R →+* S),
      Function.Surjective φ → RingHom.ker φ = p →
        ∃ P' : MaximalSpectrum (integralClosure S (FractionRing S)), ∀ x : R,
          Ring.ord (Localization.AtPrime P.asIdeal)
              (algebraMap (integralClosure R (FractionRing R)) (Localization.AtPrime P.asIdeal)
                (algebraMap R (integralClosure R (FractionRing R)) x)) =
            Ring.ord (Localization.AtPrime P'.asIdeal)
              (algebraMap (integralClosure S (FractionRing S)) (Localization.AtPrime P'.asIdeal)
                (algebraMap S (integralClosure S (FractionRing S)) (φ x)))
end
end GroundTheory.Heights₂.Heights


