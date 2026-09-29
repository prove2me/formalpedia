-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_forall_pullback_iso_of_charts_of_rigidified_of_surjective_appTop
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/826405c8-5893-5c79-bdf8-cb143cc0ead1

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_forall_pullback_iso_of_cocycle
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_pullback_iso_cocycle_of_charts_of_rigidified_of_surjective_appTop
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_of_forall_pullback_iso_of_isOpenImmersion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_forall_pullback_iso_of_charts_of_rigidified_of_surjective_appTop
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

universe u

theorem solution
    {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    (B : Fin k → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra S (B i)] [∀ i, IsLocalization.Away (r i) (B i)]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of S))
    {A' : Fin k → Scheme.{u}} (f' : ∀ i, A' i ⟶ Spec (CommRingCat.of (B i))) (ι : ∀ i, A' i ⟶ Y)
    [∀ i, IsOpenImmersion (ι i)]
    (hsq : ∀ i, CategoryTheory.IsPullback (ι i) (f' i) f (Spec.map (CommRingCat.ofHom (algebraMap S (B i)))))
    (hsurj : ∀ y : ↥Y, ∃ (i : Fin k) (x : ↥(A' i)), (ι i).base x = y)
    (hΓ : ∀ i, Function.Surjective ((f' i).appTop).hom ∧
      ∀ r : B i, Function.Surjective
        ((pullback.snd (f' i) (Spec.map (CommRingCat.ofHom (algebraMap (B i) (Localization.Away r))))).appTop).hom)
    (e : ∀ i, Spec (CommRingCat.of (B i)) ⟶ A' i) (he : ∀ i, e i ≫ f' i = 𝟙 _)
    (heagree : ∀ (i j : Fin k) (C : Type u) [CommRing C] [Algebra S C] [IsLocalization.Away (r i * r j) C]
        (ρ₁ : B i →ₐ[S] C) (ρ₂ : B j →ₐ[S] C),
        Spec.map (CommRingCat.ofHom ρ₁.toRingHom) ≫ e i ≫ ι i = Spec.map (CommRingCat.ofHom ρ₂.toRingHom) ≫ e j ≫ ι j)
    (M : ∀ i, (A' i).Modules) (hM : ∀ i, Scheme.Modules.IsInvertible (M i))
    (hrig : ∀ i, Nonempty ((Scheme.Modules.pullback (e i)).obj (M i) ≅ SheafOfModules.unit (Spec (CommRingCat.of (B i))).ringCatSheaf))
    (hloc : ∀ (i j : Fin k) (q : ↥(Limits.pullback (ι i) (ι j))), ∃ U : (Spec (CommRingCat.of S)).Opens,
        (pullback.fst (ι i) (ι j) ≫ ι i ≫ f).base q ∈ U ∧
        Nonempty
          ((Scheme.Modules.pullback ((pullback.fst (ι i) (ι j) ≫ ι i ≫ f) ⁻¹ᵁ U).ι).obj
              ((Scheme.Modules.pullback (pullback.fst (ι i) (ι j))).obj (M i)) ≅
            (Scheme.Modules.pullback ((pullback.fst (ι i) (ι j) ≫ ι i ≫ f) ⁻¹ᵁ U).ι).obj
              ((Scheme.Modules.pullback (pullback.snd (ι i) (ι j))).obj (M j)))) :
    ∃ Mg : Y.Modules, Scheme.Modules.IsInvertible Mg ∧ ∀ i, Nonempty ((Scheme.Modules.pullback (ι i)).obj Mg ≅ M i) := by
  obtain ⟨φ, hφ⟩ := AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_pullback_iso_cocycle_of_charts_of_rigidified_of_surjective_appTop r hr B f f' ι hsq hsurj hΓ e he heagree M hM hrig hloc
  have hι' : ∀ y : ↥Y, ∃ (i : ULift.{u, 0} (Fin k)) (x : ↥(A' i.down)), (ι i.down).base x = y := by
    intro y
    obtain ⟨i, x, hx⟩ := hsurj y
    exact ⟨⟨i⟩, x, hx⟩
  obtain ⟨Mg, ψ, -⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_forall_pullback_iso_of_cocycle (I := ULift.{u, 0} (Fin k)) (X := fun i => A' i.down)
      (fun i => ι i.down) hι' (fun i => M i.down) (fun i j => φ i.down j.down)
      (fun i j l T π₁₂ π₂₃ π₁₃ h₂ h₁ h₃ => hφ i.down j.down l.down T π₁₂ π₂₃ π₁₃ h₂ h₁ h₃)
  refine ⟨Mg, ?_, fun i => ⟨ψ ⟨i⟩⟩⟩
  exact AlgebraicGeometry.Scheme.Modules.IsInvertible.of_forall_pullback_iso_of_isOpenImmersion (fun i : ULift.{u, 0} (Fin k) => ι i.down) hι'
    (fun i => M i.down) (fun i => hM i.down) Mg ψ

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_forall_pullback_iso_of_charts_of_rigidified_of_surjective_appTop
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_forall_pullback_iso_of_charts_of_rigidified_of_surjective_appTop (solution)
