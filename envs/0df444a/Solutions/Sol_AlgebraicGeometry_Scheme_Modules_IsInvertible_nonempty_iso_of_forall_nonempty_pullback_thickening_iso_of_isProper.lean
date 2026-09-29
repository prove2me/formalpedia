-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_of_forall_nonempty_pullback_thickening_iso_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/5e14aeb6-f789-5bca-b880-bfdbb25a9953

import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_AdicThickening
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_compatible_pullback_iso_of_forall_nonempty_pullback_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_of_compatible_pullback_adicThickening_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_of_forall_nonempty_pullback_thickening_iso_of_isProper
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule PresheafOfModules.ExteriorPower.instModulePresheafAb"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq"
p2m_attr_erase "simp" "DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace LocIsoPermGen

noncomputable def down {X Y Z : Scheme.{u}} (k : X ⟶ Y) (q : Y ⟶ Z) (p : X ⟶ Z) (w : k ≫ q = p) {M M' : Z.Modules}
    (φ : (Scheme.Modules.pullback q).obj M ≅ (Scheme.Modules.pullback q).obj M') :
    (Scheme.Modules.pullback p).obj M ≅ (Scheme.Modules.pullback p).obj M' :=
  ((Scheme.Modules.pullbackCongr w.symm).app M ≪≫ ((Scheme.Modules.pullbackComp k q).app M).symm)
    ≪≫ (Scheme.Modules.pullback k).mapIso φ ≪≫
  ((Scheme.Modules.pullbackCongr w.symm).app M' ≪≫ ((Scheme.Modules.pullbackComp k q).app M').symm).symm

theorem bijective_algebraMap_of_iso {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (e : X ≅ Y) (c : Y ⟶ Spec (.of R))
    (h : letI := Scheme.TwoAffineOpenCover.algebraOfHom (e.hom ≫ c) ⊤
         Function.Bijective (algebraMap R Γ(X, ⊤))) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c ⊤
    Function.Bijective (algebraMap R Γ(Y, ⊤)) := by

  have key : ∀ r : R, (Scheme.TwoAffineOpenCover.algebraOfHom (e.hom ≫ c) ⊤).algebraMap r
      = e.hom.appLE ⊤ ⊤ le_top ((Scheme.TwoAffineOpenCover.algebraOfHom c ⊤).algebraMap r) := by
    intro r
    rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom, Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom]
    have hc := congrArg (fun φ => φ ((Scheme.ΓSpecIso (.of R)).inv.hom r))
      (Scheme.Hom.appLE_comp_appLE e.hom c ⊤ ⊤ ⊤ le_top le_top)
    simp only [CommRingCat.comp_apply] at hc
    exact hc.symm

  have happ : e.hom.appLE ⊤ ⊤ le_top = e.hom.app ⊤ := Scheme.Hom.appLE_eq_app e.hom
  have hiso : IsIso (e.hom.appLE ⊤ ⊤ le_top) := by
    rw [happ]
    exact (inferInstance : IsIso (e.hom.app ⊤))
  have hbij : Function.Bijective (e.hom.appLE ⊤ ⊤ le_top : Γ(Y, ⊤) → Γ(X, ⊤)) :=
    ConcreteCategory.bijective_of_isIso (e.hom.appLE ⊤ ⊤ le_top)
  have hcomp : (fun r : R => (Scheme.TwoAffineOpenCover.algebraOfHom (e.hom ≫ c) ⊤).algebraMap r)
      = (e.hom.appLE ⊤ ⊤ le_top : Γ(Y, ⊤) → Γ(X, ⊤)) ∘
          (fun r : R => (Scheme.TwoAffineOpenCover.algebraOfHom c ⊤).algebraMap r) :=
    funext key
  have h' : Function.Bijective (fun r : R => (Scheme.TwoAffineOpenCover.algebraOfHom (e.hom ≫ c) ⊤).algebraMap r) := h
  rw [hcomp] at h'
  exact (Function.Bijective.of_comp_iff' hbij _).mp h'

end LocIsoPermGen

open LocIsoPermGen in
theorem solution
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (Xk : ℕ → Scheme.{u})
    (q : ∀ k : ℕ, Xk k ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))
    (j : ∀ k : ℕ, Xk k ⟶ X)
    (hj : ∀ k : ℕ, IsPullback (j k) (q k) p
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (k + 1))))))
    (hH0 : ∀ k : ℕ,
      letI := Scheme.TwoAffineOpenCover.algebraOfHom (q k) ⊤
      Function.Bijective (algebraMap (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1)) Γ(Xk k, ⊤)))
    (𝓜 𝓜' : X.Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜) (h𝓜' : Scheme.Modules.IsInvertible 𝓜')
    (hk : ∀ k : ℕ, Nonempty ((Scheme.Modules.pullback (j k)).obj 𝓜 ≅ (Scheme.Modules.pullback (j k)).obj 𝓜')) :
    Nonempty (𝓜 ≅ 𝓜') := by

  let e : ∀ k : ℕ, Xk k ≅ adicThickening p (IsLocalRing.maximalIdeal R) k := fun k => (hj k).isoPullback
  have he₁ : ∀ k, (e k).inv ≫ j k = adicThickeningι p (IsLocalRing.maximalIdeal R) k := fun k => (hj k).isoPullback_inv_fst
  have he₂ : ∀ k, (e k).hom ≫ adicThickeningToBase p (IsLocalRing.maximalIdeal R) k = q k := fun k => (hj k).isoPullback_hom_snd

  have hk' : ∀ k : ℕ, Nonempty ((Scheme.Modules.pullback (adicThickeningι p (IsLocalRing.maximalIdeal R) k)).obj 𝓜
      ≅ (Scheme.Modules.pullback (adicThickeningι p (IsLocalRing.maximalIdeal R) k)).obj 𝓜') :=
    fun k => ⟨down (e k).inv (j k) _ (he₁ k) (hk k).some⟩

  have hH0' : ∀ k : ℕ, letI := Scheme.TwoAffineOpenCover.algebraOfHom (adicThickeningToBase p (IsLocalRing.maximalIdeal R) k) ⊤
      Function.Bijective (algebraMap (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1)) Γ(adicThickening p (IsLocalRing.maximalIdeal R) k, ⊤)) := by
    intro k
    refine bijective_algebraMap_of_iso (e k) _ ?_
    rw [he₂ k]
    exact hH0 k

  obtain ⟨φ, hφ⟩ := AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_compatible_pullback_iso_of_forall_nonempty_pullback_iso
    R (fun k => adicThickening p (IsLocalRing.maximalIdeal R) k) (fun k => adicThickeningToBase p _ k)
    (fun k => adicThickeningι p _ k) (fun k => adicThickeningTransition p _ k)
    (fun k => adicThickeningTransition_ι p _ k) (fun k => adicThickeningTransition_toBase p _ k) hH0' 𝓜 𝓜' h𝓜 h𝓜' hk'
  exact AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_of_compatible_pullback_adicThickening_iso
    R (IsLocalRing.maximalIdeal R) p 𝓜 𝓜' h𝓜 h𝓜' φ hφ

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_of_forall_nonempty_pullback_thickening_iso_of_isProper
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_of_forall_nonempty_pullback_thickening_iso_of_isProper (solution)
