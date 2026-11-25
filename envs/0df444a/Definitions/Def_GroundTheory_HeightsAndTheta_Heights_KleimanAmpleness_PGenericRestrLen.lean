-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGenericRestrLen
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGenericRestrLen
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T07:03:45.976897+00:00
-- url     : https://prove2.me/theorems/1cca2594-321d-4a33-b93e-981fa9890b19
-- title:
--   PGeneric Restr Len
-- statement:
--   Definitions and structural lemmas for PGeneric Restr Len, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGenericRestrLen.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsGenericRestrLen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExtendTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFiniteSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFibreSectionsFlat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
section Localisation
variable {S : Type u} [CommRing S] {F : Type u} [Field F] [Algebra S F] [IsFractionRing S F]
  {Ω : Type w} [Field Ω] [Algebra S Ω] [Algebra F Ω] [IsScalarTower S F Ω]
variable (F) in

def spanQuotMap (A B : Submodule S Ω) :
    (A ⧸ B.comap A.subtype) →ₗ[S]
      (Submodule.span F (A : Set Ω) ⧸
        (Submodule.span F (B : Set Ω)).comap (Submodule.span F (A : Set Ω)).subtype) :=
  (B.comap A.subtype).liftQ
    ((((Submodule.span F (B : Set Ω)).comap (Submodule.span F (A : Set Ω)).subtype).mkQ.restrictScalars S) ∘ₗ
      { toFun := fun a => ⟨a, Submodule.subset_span a.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl })
    (fun _a ha => LinearMap.mem_ker.mpr ((Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ha)))
end Localisation
section Ideal
variable {S : Type u} [CommRing S] {F : Type u} [Field F] [Algebra S F] {N : ℕ}
variable [IsFractionRing S F] {Ω : Type w} [Field Ω] [Algebra S Ω] [Algebra F Ω] [IsScalarTower S F Ω]
end Ideal
end
end GroundTheory.Heights₂.Heights.Kleiman


