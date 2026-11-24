-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthLocalizedQuotient
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthLocalizedQuotient
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:53.268809+00:00
-- url     : https://prove2.me/theorems/7939722b-3373-4913-ad15-b12b236d822f
-- title:
--   St Length Localized Quotient
-- statement:
--   Definitions and structural lemmas for St Length Localized Quotient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StLengthLocalizedQuotient.lean

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
def LengthLocalizedQuotient.Statement : Prop :=
  ∀ (B : Type u) [CommRing B] [IsNoetherianRing B] (P : Ideal B) [P.IsPrime] (y : B),
    minimalPrimes B = {P} → (∀ s ∉ P, s ∈ nonZeroDivisors B) → y ∉ P →
    ∀ (Q : Ideal (B ⧸ Ideal.span {y})) [Q.IsPrime], Q.comap (Ideal.Quotient.mk _) = P ⊔ Ideal.span {y} →
      Module.length (Localization.AtPrime Q) (Localization.AtPrime Q) =
        Module.length (Localization.AtPrime P) (Localization.AtPrime P)
end GroundTheory.Heights₂.Heights


