-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:06.270272+00:00
-- url     : https://prove2.me/theorems/939a034e-9987-4451-bc47-d5b7ba75993e
-- title:
--   Exists Completion Point Closed Point Mem Of Smooth
-- statement:
--   Definitions and structural lemmas for Exists Completion Point Closed Point Mem Of Smooth, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsCompletionPointClosedPointMemOfSmooth.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
universe u
section Lift
variable {X S : Scheme.{u}} (f : X ⟶ S)
noncomputable def reducePoint {B C : CommRingCat.{u}} (π : B ⟶ C) (s : Spec B ⟶ S)
    (x : {x : Spec B ⟶ X // x ≫ f = s}) : {x₀ : Spec C ⟶ X // x₀ ≫ f = Spec.map π ≫ s} :=
  ⟨Spec.map π ≫ x.1, by rw [Category.assoc, x.2]⟩
section Quotient
variable (B : Type u) [CommRing B] [IsLocalRing B] (I : Ideal B) [HenselianRing B I]
  (s : Spec (.of B) ⟶ S)
end Quotient
section Residue
variable (B : Type u) [CommRing B] [HenselianLocalRing B] (s : Spec (.of B) ⟶ S)
end Residue
end Lift
section QuasiSection
variable {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]
end QuasiSection
section Field
end Field
section DiscreteValuation
variable {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]
end DiscreteValuation
section SpecialFibre
variable {V : Type u} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of V)) [Smooth f]
  (U : (pullback f (Spec.map (CommRingCat.ofHom (residue V)))).Opens)
end SpecialFibre
section Main
end Main
end GlobalTheory


