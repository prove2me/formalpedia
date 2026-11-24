-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalizeQuotientStages
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalizeQuotientStages
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:10.181546+00:00
-- url     : https://prove2.me/theorems/50031987-a108-4ebe-9ec1-6390dd3f05c7
-- title:
--   St Localize Quotient Stages
-- statement:
--   Definitions and structural lemmas for St Localize Quotient Stages, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StLocalizeQuotientStages.lean

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
def LocalizeQuotientStages.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (m W I : Ideal R) [m.IsPrime] [W.IsPrime], W ≤ m → I ≤ W →
    ∀ (P : Ideal (Localization.AtPrime m ⧸ I.map (algebraMap R (Localization.AtPrime m)))) [P.IsPrime],
      W.map ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
        (algebraMap R (Localization.AtPrime m))) = P →
      Module.length (Localization.AtPrime P) (Localization.AtPrime P) =
        Module.length (Localization.AtPrime W)
          (Localization.AtPrime W ⧸ I.map (algebraMap R (Localization.AtPrime W)))
end
end GroundTheory.Heights₂.Heights


