-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.trans_eq_of_pullback_mapIso_eq_of_surjective_appTop
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/5f48beab-f9cc-5dc9-8f8f-8f993c0208ef

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_iso_eq_of_pullback_section_map_eq_of_surjective_appTop
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_trans_eq_of_pullback_mapIso_eq_of_surjective_appTop
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    (e : Spec (CommRingCat.of S) ⟶ A) (he : e ≫ f = 𝟙 _)
    (hΓ₀ : Function.Surjective (f.appTop).hom)
    (L₁ L₂ L₃ : A.Modules) (hL₁ : Scheme.Modules.IsInvertible L₁)
    (ρ₁ : (Scheme.Modules.pullback e).obj L₁ ≅ SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf)
    (ρ₂ : (Scheme.Modules.pullback e).obj L₂ ≅ SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf)
    (ρ₃ : (Scheme.Modules.pullback e).obj L₃ ≅ SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf)
    (φ₁₂ : L₁ ≅ L₂) (φ₂₃ : L₂ ≅ L₃) (φ₁₃ : L₁ ≅ L₃)
    (h₁₂ : (Scheme.Modules.pullback e).mapIso φ₁₂ = ρ₁ ≪≫ ρ₂.symm)
    (h₂₃ : (Scheme.Modules.pullback e).mapIso φ₂₃ = ρ₂ ≪≫ ρ₃.symm)
    (h₁₃ : (Scheme.Modules.pullback e).mapIso φ₁₃ = ρ₁ ≪≫ ρ₃.symm) :
    φ₁₂ ≪≫ φ₂₃ = φ₁₃ := by
  apply AlgebraicGeometry.Scheme.Modules.IsInvertible.iso_eq_of_pullback_section_map_eq_of_surjective_appTop f e he hΓ₀ L₁ L₃ hL₁
  have e12 := congrArg Iso.hom h₁₂
  have e23 := congrArg Iso.hom h₂₃
  have e13 := congrArg Iso.hom h₁₃
  simp only [Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom] at e12 e23 e13
  rw [Iso.trans_hom, Functor.map_comp, e12, e23, e13]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_trans_eq_of_pullback_mapIso_eq_of_surjective_appTop
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_trans_eq_of_pullback_mapIso_eq_of_surjective_appTop (solution)
