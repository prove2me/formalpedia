-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalizationAtPrimeQuotient
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalizationAtPrimeQuotient
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:38.111935+00:00
-- url     : https://prove2.me/theorems/f162e43b-6f1e-4e3c-a094-5e53353ebba8
-- title:
--   St Localization At Prime Quotient
-- statement:
--   Definitions and structural lemmas for St Localization At Prime Quotient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StLocalizationAtPrimeQuotient.lean

import Mathlib
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
universe u
noncomputable section
def LocalizationAtPrimeQuotient.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] (I : Ideal A) (T : Submonoid (A ⧸ I)) (P : Ideal (Localization T)) [P.IsPrime]
    (W : Ideal A) [W.IsPrime],
    P.comap ((algebraMap (A ⧸ I) (Localization T)).comp (Ideal.Quotient.mk I)) = W →
      ∃ e : Localization.AtPrime P ≃+* (Localization.AtPrime W ⧸ I.map (algebraMap A (Localization.AtPrime W))),
        ∀ a : A,
          e (algebraMap (Localization T) (Localization.AtPrime P)
              (algebraMap (A ⧸ I) (Localization T) (Ideal.Quotient.mk I a))) =
            Ideal.Quotient.mk (I.map (algebraMap A (Localization.AtPrime W)))
              (algebraMap A (Localization.AtPrime W) a)
end
end GroundTheory.Heights₂.Heights


