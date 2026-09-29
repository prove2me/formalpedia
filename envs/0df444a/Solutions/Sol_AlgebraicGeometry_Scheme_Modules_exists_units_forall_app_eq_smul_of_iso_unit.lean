-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_units_forall_app_eq_smul_of_iso_unit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/85b47a31-db2b-5368-b636-4feb05d31b03

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_forall_app_eq_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_eq_one_of_forall_smul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_units_forall_app_eq_smul_of_iso_unit
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

theorem solution
    {X : Scheme.{u}} (γ : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ≅ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) :
    ∃ u : Γ(X, ⊤)ˣ, ∀ (U : X.Opens) (s : Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U)),
      Scheme.Modules.Hom.app γ.hom U s = X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (u : Γ(X, ⊤)) • s := by
  have hL : Scheme.Modules.IsInvertible (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
    Scheme.Modules.isInvertible_unit X
  obtain ⟨u, hu⟩ := hL.exists_forall_app_eq_smul γ.hom
  obtain ⟨v, hv⟩ := hL.exists_forall_app_eq_smul γ.inv
  have hinv : ∀ (U : X.Opens) (s : Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U)),
      Scheme.Modules.Hom.app γ.inv U (Scheme.Modules.Hom.app γ.hom U s) = s := by
    intro U s
    have h := congrArg (fun f => Scheme.Modules.Hom.app f U s) γ.hom_inv_id
    simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app, CategoryTheory.comp_apply,
      CategoryTheory.id_apply] at h
    exact h
  have hvu : v * u = 1 := by
    apply hL.eq_one_of_forall_smul_eq
    intro U s
    rw [map_mul, mul_smul, ← hu U s, ← hv U (Scheme.Modules.Hom.app γ.hom U s)]
    exact hinv U s
  refine ⟨⟨u, v, ?_, hvu⟩, ?_⟩
  · rw [mul_comm]; exact hvu
  · intro U s
    exact hu U s

end S_AlgebraicGeometry_Scheme_Modules_exists_units_forall_app_eq_smul_of_iso_unit
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_units_forall_app_eq_smul_of_iso_unit (solution)
