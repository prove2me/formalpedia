-- Prove2me | solution 1 for AlgebraicGeometry.PolarisedAbelianScheme.nonempty_iso_of_pullback_locally_iso_of_faithfullyFlat_of_rigidified
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/5d096947-db0b-587b-b4da-d2288120d48e

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_of_locally_of_pullback_section_trivial
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_map_eq_of_isPullback_of_faithfullyFlat
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_surjective_appTop_and_pullback_snd_away
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_iso_pullback_map_hom_eq_of_pullback_section_trivial
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_map_cocycle_of_pullback_section_map_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_nonempty_iso_of_pullback_locally_iso_of_faithfullyFlat_of_rigidified
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

universe u

noncomputable section

namespace RLDAux

def PC {X Y Z : Scheme.{0}} (k : X ⟶ Y) (l : Y ⟶ Z) (M : Z.Modules) :
    (Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback l).obj M) ≅ (Scheme.Modules.pullback (k ≫ l)).obj M :=
  (Scheme.Modules.pullbackComp k l).app M

def CG {X Y : Scheme.{0}} {k l : X ⟶ Y} (h : k = l) (M : Y.Modules) :
    (Scheme.Modules.pullback k).obj M ≅ (Scheme.Modules.pullback l).obj M :=
  (Scheme.Modules.pullbackCongr h).app M

theorem specMap_comp {S S' S'' : Type} [CommRing S] [CommRing S'] [CommRing S''] (φ : S →+* S') (ψ : S' →+* S'') :
    Spec.map (CommRingCat.ofHom (ψ.comp φ)) = Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem includeLeftRingHom_comp_algebraMap {S S' : Type} [CommRing S] [CommRing S'] [Algebra S S'] :
    (Algebra.TensorProduct.includeLeftRingHom : S' →+* S' ⊗[S] S').comp (algebraMap S S') =
      (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom.comp (algebraMap S S') := by
  ext r
  exact ((Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S').commutes r).trans
    ((Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').commutes r).symm

end RLDAux

open RLDAux in
theorem solution
    {g d n : ℕ} {S S' : Type} [CommRing S] [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    (u : PolarisedAbelianScheme g d n S) (v : PolarisedAbelianScheme g d n S') (c : v.A ⟶ u.A)
    (hc : CategoryTheory.IsPullback c v.f u.f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (L M : u.A.Modules) (hL : Scheme.Modules.IsInvertible L) (hM : Scheme.Modules.IsInvertible M)
    (hLe : Nonempty ((Scheme.Modules.pullback (u.L.one (𝟙 _)).1).obj L ≅ SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf))
    (hMe : Nonempty ((Scheme.Modules.pullback (u.L.one (𝟙 _)).1).obj M ≅ SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf))
    (hloc : ∀ s : ↥(Spec (CommRingCat.of S')), ∃ U : (Spec (CommRingCat.of S')).Opens, s ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (v.f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback c).obj L) ≅
        (Scheme.Modules.pullback (v.f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback c).obj M))) :
    Nonempty (L ≅ M) := by
  classical
  obtain ⟨tL⟩ := hLe
  obtain ⟨tM⟩ := hMe
  set e := (u.L.one (𝟙 _)).1 with he_def
  have he : e ≫ u.f = 𝟙 _ := (u.L.one (𝟙 _)).2
  set σ := Spec.map (CommRingCat.ofHom (algebraMap S S')) with hσ

  have w₀ : (σ ≫ e) ≫ u.f = 𝟙 _ ≫ σ := by rw [Category.assoc, he, Category.comp_id, Category.id_comp]
  let e' : Spec (CommRingCat.of S') ⟶ v.A := hc.lift (σ ≫ e) (𝟙 _) w₀
  have he'c : e' ≫ c = σ ≫ e := hc.lift_fst _ _ _
  have he'f : e' ≫ v.f = 𝟙 _ := hc.lift_snd _ _ _

  let γ : ∀ N : u.A.Modules, (Scheme.Modules.pullback e').obj ((Scheme.Modules.pullback c).obj N) ≅
      (Scheme.Modules.pullback σ).obj ((Scheme.Modules.pullback e).obj N) :=
    fun N => PC e' c N ≪≫ CG he'c N ≪≫ (PC σ e N).symm
  let tL' : (Scheme.Modules.pullback e').obj ((Scheme.Modules.pullback c).obj L) ≅
      SheafOfModules.unit (Spec (CommRingCat.of S')).ringCatSheaf :=
    γ L ≪≫ (Scheme.Modules.pullback σ).mapIso tL ≪≫ Scheme.Modules.pullbackUnitIso σ
  let tM' : (Scheme.Modules.pullback e').obj ((Scheme.Modules.pullback c).obj M) ≅
      SheafOfModules.unit (Spec (CommRingCat.of S')).ringCatSheaf :=
    γ M ≪≫ (Scheme.Modules.pullback σ).mapIso tM ≪≫ Scheme.Modules.pullbackUnitIso σ

  have hΓ := GoodReductionJacobian.AbelianSchemePropertyBundle.surjective_appTop_and_pullback_snd_away v.bundle
  obtain ⟨α₀⟩ := AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_of_locally_of_pullback_section_trivial
    v.f e' he'f hΓ.2 _ _ (hL.pullback c) (hM.pullback c) ⟨tL'⟩ ⟨tM'⟩ hloc

  let NCiso : ∀ (L M : u.A.Modules)
      (τL : (Scheme.Modules.pullback e).obj L ≅ SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf)
      (τM : (Scheme.Modules.pullback e).obj M ≅ SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf),
      (Scheme.Modules.pullback e').obj ((Scheme.Modules.pullback c).obj L) ≅
        (Scheme.Modules.pullback e').obj ((Scheme.Modules.pullback c).obj M) := fun L M τL τM =>
    (Scheme.Modules.pullbackComp e' c).app L ≪≫ (Scheme.Modules.pullbackCongr he'c).app L ≪≫
        ((Scheme.Modules.pullbackComp (Spec.map (CommRingCat.ofHom (algebraMap S S'))) e).app L).symm ≪≫
        (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap S S')))).mapIso (τL ≪≫ τM.symm) ≪≫
        (Scheme.Modules.pullbackComp (Spec.map (CommRingCat.ofHom (algebraMap S S'))) e).app M ≪≫
        ((Scheme.Modules.pullbackCongr he'c).app M).symm ≪≫ ((Scheme.Modules.pullbackComp e' c).app M).symm
  let β' := NCiso L M tL tM
  let μ : (Scheme.Modules.pullback e').obj ((Scheme.Modules.pullback c).obj L) ≅
      (Scheme.Modules.pullback e').obj ((Scheme.Modules.pullback c).obj L) :=
    (Scheme.Modules.pullback e').mapIso α₀ ≪≫ β'.symm
  obtain ⟨θ, hθ⟩ := AlgebraicGeometry.Scheme.Modules.exists_iso_pullback_map_hom_eq_of_pullback_section_trivial
    v.f e' he'f ((Scheme.Modules.pullback c).obj L) ⟨tL'⟩ μ
  let α : (Scheme.Modules.pullback c).obj L ≅ (Scheme.Modules.pullback c).obj M := θ.symm ≪≫ α₀
  have hθ' : (Scheme.Modules.pullback e').mapIso θ = μ := Iso.ext hθ
  have hnorm : (Scheme.Modules.pullback e').map α.hom = β'.hom := by
    show (Scheme.Modules.pullback e').map (θ.inv ≫ α₀.hom) = β'.hom
    rw [Functor.map_comp, ← Functor.mapIso_inv, hθ']
    simp [μ]
  have hnormI : (Scheme.Modules.pullback e').mapIso α = β' := Iso.ext hnorm
  have hnorm' : (Scheme.Modules.pullback e').map α.symm.hom = (NCiso M L tM tL).hom := by
    show (Scheme.Modules.pullback e').map α.inv = (NCiso M L tM tL).hom
    rw [← Functor.mapIso_inv, hnormI]
    simp only [β', NCiso, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom, Functor.mapIso_inv,
      Functor.mapIso_hom, Category.assoc]

  set i₁ := (Algebra.TensorProduct.includeLeftRingHom : S' →+* S' ⊗[S] S') with hi₁
  set i₂ := (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom with hi₂
  have hS : Spec.map (CommRingCat.ofHom i₁) ≫ σ = Spec.map (CommRingCat.ofHom i₂) ≫ σ := by
    rw [hσ, ← specMap_comp, ← specMap_comp, hi₁, hi₂, includeLeftRingHom_comp_algebraMap]
  obtain ⟨w, hw⟩ := PolarisedAbelianScheme.exists_isPullback i₁ v
  obtain ⟨q₁, hq₁, -, -, -⟩ := hw
  have wq : (q₁ ≫ c) ≫ u.f = (w.f ≫ Spec.map (CommRingCat.ofHom i₂)) ≫ σ := by
    rw [Category.assoc, hc.w, ← Category.assoc, hq₁.w, Category.assoc, Category.assoc, hS]
  let q₂ := hc.lift (q₁ ≫ c) (w.f ≫ Spec.map (CommRingCat.ofHom i₂)) wq
  have hq : q₁ ≫ c = q₂ ≫ c := (hc.lift_fst _ _ _).symm
  have hq₂f : q₂ ≫ v.f = w.f ≫ Spec.map (CommRingCat.ofHom i₂) := hc.lift_snd _ _ _
  have hq₂ : CategoryTheory.IsPullback q₂ w.f v.f (Spec.map (CommRingCat.ofHom i₂)) := by
    refine IsPullback.of_right ?_ hq₂f hc
    rw [← hq, ← hS]
    exact hq₁.paste_horiz hc
  have hΓ'' := (GoodReductionJacobian.AbelianSchemePropertyBundle.surjective_appTop_and_pullback_snd_away w.bundle).1

  have hcoc := AlgebraicGeometry.Scheme.Modules.IsInvertible.pullback_map_cocycle_of_pullback_section_map_eq
    u.f v.f c hc w.f q₁ q₂ hq₁ hq₂ hq hΓ'' e he e' he'f he'c L M hL hM tL tM α hnorm
  have hcoc' := AlgebraicGeometry.Scheme.Modules.IsInvertible.pullback_map_cocycle_of_pullback_section_map_eq
    u.f v.f c hc w.f q₁ q₂ hq₁ hq₂ hq hΓ'' e he e' he'f he'c M L hM hL tM tL α.symm hnorm'

  obtain ⟨β, hβ, -⟩ := AlgebraicGeometry.Scheme.Modules.IsInvertible.existsUnique_map_eq_of_isPullback_of_faithfullyFlat
    u.f v.f c hc w.f q₁ q₂ hq₁ hq₂ hq L M hL hM α.hom hcoc
  obtain ⟨β₂, hβ₂, -⟩ := AlgebraicGeometry.Scheme.Modules.IsInvertible.existsUnique_map_eq_of_isPullback_of_faithfullyFlat
    u.f v.f c hc w.f q₁ q₂ hq₁ hq₂ hq M L hM hL α.symm.hom hcoc'
  have hid : ∀ (N : u.A.Modules) (hN : Scheme.Modules.IsInvertible N) (x : N ⟶ N),
      (Scheme.Modules.pullback c).map x = 𝟙 _ → x = 𝟙 _ := by
    intro N hN x hx
    have hc1 : (Scheme.Modules.pullback q₁).map (𝟙 ((Scheme.Modules.pullback c).obj N)) ≫
        ((Scheme.Modules.pullbackComp q₁ c).app N).hom ≫ ((Scheme.Modules.pullbackCongr hq).app N).hom ≫
          ((Scheme.Modules.pullbackComp q₂ c).app N).inv =
        ((Scheme.Modules.pullbackComp q₁ c).app N).hom ≫ ((Scheme.Modules.pullbackCongr hq).app N).hom ≫
          ((Scheme.Modules.pullbackComp q₂ c).app N).inv ≫ (Scheme.Modules.pullback q₂).map (𝟙 _) := by
      simp only [CategoryTheory.Functor.map_id, Category.id_comp]
      erw [Category.comp_id]
    obtain ⟨β₀, -, hu⟩ := AlgebraicGeometry.Scheme.Modules.IsInvertible.existsUnique_map_eq_of_isPullback_of_faithfullyFlat
      u.f v.f c hc w.f q₁ q₂ hq₁ hq₂ hq N N hN hN (𝟙 _) hc1
    exact (hu x hx).trans (hu (𝟙 _) (CategoryTheory.Functor.map_id _ _)).symm
  have h12 : β ≫ β₂ = 𝟙 _ := hid L hL _ (by rw [Functor.map_comp, hβ, hβ₂]; exact α.hom_inv_id)
  have h21 : β₂ ≫ β = 𝟙 _ := hid M hM _ (by rw [Functor.map_comp, hβ₂, hβ]; exact α.inv_hom_id)
  exact ⟨⟨β, β₂, h12, h21⟩⟩

end

end S_AlgebraicGeometry_PolarisedAbelianScheme_nonempty_iso_of_pullback_locally_iso_of_faithfullyFlat_of_rigidified
end P2MW
export P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_nonempty_iso_of_pullback_locally_iso_of_faithfullyFlat_of_rigidified (solution)
