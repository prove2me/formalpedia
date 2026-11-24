-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthLocalizedLocalized
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthLocalizedLocalized
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:25:25.490509+00:00
-- url     : https://prove2.me/theorems/0e04310e-5bfd-47d8-9968-b3f2d60b4e43
-- title:
--   St Length Localized Localized
-- statement:
--   Definitions and structural lemmas for St Length Localized Localized, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StLengthLocalizedLocalized.lean

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
universe u v
def LengthLocalizedLocalized.Statement : Prop :=
  ∀ (B : Type u) [CommRing B] (P Q : Ideal B) [P.IsPrime] [Q.IsPrime]
    [(P.map (algebraMap B (Localization.AtPrime Q))).IsPrime]
    (M : Type v) [AddCommGroup M] [Module B M],
    P ≤ Q →
      Module.length (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
          (LocalizedModule (P.map (algebraMap B (Localization.AtPrime Q))).primeCompl
            (LocalizedModule Q.primeCompl M)) =
        Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl M)
end GroundTheory.Heights₂.Heights


