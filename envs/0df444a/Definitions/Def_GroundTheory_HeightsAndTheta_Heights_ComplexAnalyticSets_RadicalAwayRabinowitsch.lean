-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_RadicalAwayRabinowitsch
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_RadicalAwayRabinowitsch
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:59:01.128277+00:00
-- url     : https://prove2.me/theorems/d3df0922-8976-4c7e-9c13-2cf668501227
-- title:
--   Radical Away Rabinowitsch
-- statement:
--   Definitions and structural lemmas for Radical Away Rabinowitsch, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/RadicalAwayRabinowitsch.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreRadicalAway
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
open MvPolynomial
noncomputable section
variable {R : Type*} [CommRing R] {ι : Type*}
def rabinowitschIdeal (K : Ideal (MvPolynomial ι R)) (g : MvPolynomial ι R) :
    Ideal (MvPolynomial (Option ι) R) :=
  K.map (rename (R := R) some).toRingHom ⊔ Ideal.span {X none * rename some g - 1}
def rabinowitschEval (K : Ideal (MvPolynomial ι R)) (g : MvPolynomial ι R) :
    MvPolynomial (Option ι) R →+* Localization.Away (Ideal.Quotient.mk K g) :=
  eval₂Hom ((algebraMap (MvPolynomial ι R ⧸ K) _).comp ((Ideal.Quotient.mk K).comp C))
    fun o => Option.elim o (IsLocalization.Away.invSelf (Ideal.Quotient.mk K g))
      fun i => algebraMap (MvPolynomial ι R ⧸ K) _ (Ideal.Quotient.mk K (X i))
end
end GroundTheory.Heights₂.Heights


