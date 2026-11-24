-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsLocalizedQuotientLength
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsLocalizedQuotientLength
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:09:58.203192+00:00
-- url     : https://prove2.me/theorems/e2584253-b027-4a01-8256-5a35bbd4e538
-- title:
--   Statements Localized Quotient Length
-- statement:
--   Definitions and structural lemmas for Statements Localized Quotient Length, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsLocalizedQuotientLength.lean

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
namespace GroundTheory.Heights₂.Heights.FieldNumbers
noncomputable section
universe u v
def LocalizedQuotientLength.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (P W : Ideal S) [W.IsPrime] (x : S) (R : Type v) [CommRing R]
    [Algebra (S ⧸ P) R], IsLocalization (W.primeCompl.map (Ideal.Quotient.mk P)) R →
      Module.length (Localization.AtPrime W)
          (LocalizedModule W.primeCompl (S ⧸ (P ⊔ Ideal.span {x}))) =
        Module.length R (R ⧸ Ideal.span {algebraMap (S ⧸ P) R (Ideal.Quotient.mk P x)})
end
end GroundTheory.Heights₂.Heights.FieldNumbers


