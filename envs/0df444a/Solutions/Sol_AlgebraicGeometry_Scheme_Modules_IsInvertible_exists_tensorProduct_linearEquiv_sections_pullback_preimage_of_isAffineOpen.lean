-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_tensorProduct_linearEquiv_sections_pullback_preimage_of_isAffineOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/8cd04d23-96a6-5e7e-9586-aafa9899a4c3

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isAffineOpen_preimage_and_isPushout_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensorProduct_linearEquiv_sections_pullback_preimage_of_isAffineOpen
p2m_attr_erase "instance" "PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module"
p2m_attr_erase "instance" "TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec"
p2m_attr_erase "simp" "TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

theorem solution
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
    {X X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S))
    (f' : X' ⟶ Spec (CommRingCat.of S')) (c : X' ⟶ X)
    (hc : IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) (U : X.Opens) (hU : IsAffineOpen U) :
    letI : Algebra S Γ(X, U) := ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appLE ⊤ U le_top).hom.toAlgebra
    letI : Module S Γ(M, U) := Module.compHom _ (algebraMap S Γ(X, U))
    letI : Algebra S' Γ(X', c ⁻¹ᵁ U) :=
      ((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appLE ⊤ (c ⁻¹ᵁ U) le_top).hom.toAlgebra
    letI : Module S' Γ((Scheme.Modules.pullback c).obj M, c ⁻¹ᵁ U) :=
      Module.compHom _ (algebraMap S' Γ(X', c ⁻¹ᵁ U))
    ∃ β : S' ⊗[S] Γ(M, U) ≃ₗ[S'] Γ((Scheme.Modules.pullback c).obj M, c ⁻¹ᵁ U),
      ∀ s : Γ(M, U), β (1 ⊗ₜ s) = (((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app M).app U) s := by

  obtain ⟨hcU, hpush⟩ :=
    AlgebraicGeometry.Scheme.Hom.isAffineOpen_preimage_and_isPushout_of_isPullback f f' c hc U hU

  obtain ⟨β₀, hβ₀⟩ :=
    AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_baseChange_sections_linearEquiv_pullback
      c hM U hU hcU

  letI iA : Algebra S Γ(X, U) :=
    ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appLE ⊤ U le_top).hom.toAlgebra
  letI : Module S Γ(M, U) := Module.compHom _ (algebraMap S Γ(X, U))
  letI iB : Algebra S' Γ(X', c ⁻¹ᵁ U) :=
    ((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appLE ⊤ (c ⁻¹ᵁ U) le_top).hom.toAlgebra
  letI : Module S' Γ((Scheme.Modules.pullback c).obj M, c ⁻¹ᵁ U) :=
    Module.compHom _ (algebraMap S' Γ(X', c ⁻¹ᵁ U))

  letI iAB : Algebra Γ(X, U) Γ(X', c ⁻¹ᵁ U) := (c.app U).hom.toAlgebra
  letI iSB : Algebra S Γ(X', c ⁻¹ᵁ U) :=
    ((algebraMap Γ(X, U) Γ(X', c ⁻¹ᵁ U)).comp (algebraMap S Γ(X, U))).toAlgebra
  haveI tSAB : IsScalarTower S Γ(X, U) Γ(X', c ⁻¹ᵁ U) := IsScalarTower.of_algebraMap_eq' rfl

  have hw : f' ≫ Spec.map (CommRingCat.ofHom (algebraMap S S')) = c ≫ f := hc.w.symm
  have h1 : (Spec.map (CommRingCat.ofHom (algebraMap S S'))).appTop ≫ f'.appLE ⊤ (c ⁻¹ᵁ U) le_top =
      (c ≫ f).appLE ⊤ (c ⁻¹ᵁ U) le_top := by
    change (Spec.map (CommRingCat.ofHom (algebraMap S S'))).appTop ≫
        (f'.appTop ≫ X'.presheaf.map (homOfLE le_top).op) =
      (c ≫ f).appTop ≫ X'.presheaf.map (homOfLE le_top).op
    rw [← Category.assoc, ← Scheme.Hom.comp_appTop, hw]
  have h3 : f.appLE ⊤ U le_top ≫ c.app U = (c ≫ f).appLE ⊤ (c ⁻¹ᵁ U) le_top := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  have E : CommRingCat.ofHom (algebraMap S S') ≫
      ((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appLE ⊤ (c ⁻¹ᵁ U) le_top) =
      ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appLE ⊤ U le_top) ≫ c.app U := by
    rw [Scheme.ΓSpecIso_inv_naturality_assoc, Category.assoc, h1, h3]
  haveI tSS'B : IsScalarTower S S' Γ(X', c ⁻¹ᵁ U) :=
    IsScalarTower.of_algebraMap_eq fun s => (congrArg (fun k => k.hom s) E).symm
  haveI : IsScalarTower S Γ(X, U) Γ(M, U) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : IsScalarTower S' Γ(X', c ⁻¹ᵁ U) Γ((Scheme.Modules.pullback c).obj M, c ⁻¹ᵁ U) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl

  have key : c.appLE U (c ⁻¹ᵁ U) le_rfl = c.app U := Scheme.Hom.appLE_eq_app c
  have tSAB' : (letI : Algebra Γ(X, U) Γ(X', c ⁻¹ᵁ U) := (c.appLE U (c ⁻¹ᵁ U) le_rfl).hom.toAlgebra
      IsScalarTower S Γ(X, U) Γ(X', c ⁻¹ᵁ U)) := by
    letI : Algebra Γ(X, U) Γ(X', c ⁻¹ᵁ U) := (c.appLE U (c ⁻¹ᵁ U) le_rfl).hom.toAlgebra
    exact IsScalarTower.of_algebraMap_eq fun s => by
      change _ = (c.appLE U (c ⁻¹ᵁ U) le_rfl).hom (algebraMap S Γ(X, U) s)
      rw [key]; rfl
  haveI : Algebra.IsPushout S S' Γ(X, U) Γ(X', c ⁻¹ᵁ U) := by
    have hP := @hpush iSB tSS'B tSAB'
    convert hP using 2 <;> try rfl
    rw [key]

  refine ⟨(Algebra.IsPushout.cancelBaseChange S S' Γ(X, U) Γ(X', c ⁻¹ᵁ U) Γ(M, U)).symm ≪≫ₗ
    β₀.restrictScalars S', fun s => ?_⟩
  rw [LinearEquiv.trans_apply, Algebra.IsPushout.cancelBaseChange_symm_tmul, map_one,
    LinearEquiv.restrictScalars_apply, hβ₀]

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensorProduct_linearEquiv_sections_pullback_preimage_of_isAffineOpen
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensorProduct_linearEquiv_sections_pullback_preimage_of_isAffineOpen (solution)
