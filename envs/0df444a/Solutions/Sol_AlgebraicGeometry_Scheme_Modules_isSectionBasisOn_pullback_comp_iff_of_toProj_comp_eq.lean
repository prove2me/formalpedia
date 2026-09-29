-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.isSectionBasisOn_pullback_comp_iff_of_toProj_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/4ac7e9c9-c92d-5547-9b44-31ea2b8229a3

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_projPresentation_pullback_sigma_eq_toProj_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_sigma_eq_toProj_eq_comp_map_of_algebraMap
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_nonempty_iso_of_toProj_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_unit_smul_eq_of_toProj_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackComp_hom_app_pullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_isSectionBasisOn_pullback_comp_iff_of_toProj_comp_eq
p2m_attr_erase "instance" "AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free ProjSpaceCech.GradedModule.H.module"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory"
p2m_attr_erase "simp" "AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app"
p2m_attr_erase "simp" "PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LinSysSol

p2m_open "AlgebraicGeometry.Scheme.Modules"

def castBase {R : Type} [CommRing R] {X : Scheme.{0}} {f f' : X ⟶ Spec (.of R)} (h : f = f')
    {M : X.Modules} {N : ℕ} (𝔓 : M.ProjPresentation f N) : M.ProjPresentation f' N := h ▸ 𝔓

theorem castBase_toProj {R : Type} [CommRing R] {X : Scheme.{0}} {f f' : X ⟶ Spec (.of R)} (h : f = f')
    {M : X.Modules} {N : ℕ} (𝔓 : M.ProjPresentation f N) : (castBase h 𝔓).toProj = 𝔓.toProj := by
  subst h; rfl

theorem castBase_σ {R : Type} [CommRing R] {X : Scheme.{0}} {f f' : X ⟶ Spec (.of R)} (h : f = f')
    {M : X.Modules} {N : ℕ} (𝔓 : M.ProjPresentation f N) (i : Fin (N + 1)) : (castBase h 𝔓).σ i = 𝔓.σ i := by
  subst h; rfl

theorem iso_inv_hom_apply {X : Scheme.{0}} {M N : X.Modules} (e : M ≅ N) (U : X.Opens) (x : Γ(M, U)) :
    (e.inv.app U) ((e.hom.app U) x) = x := by
  change ((e.hom.app U) ≫ (e.inv.app U)) x = x
  rw [← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app]
  rfl

theorem isSectionBasisOn_iff_of_iso {S : Type} [CommRing S] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of S))
    {M M' : X.Modules} (V : X.Opens) (φ : M ≅ M') (u : Γ(X, V)) (hu : IsUnit u) {m : ℕ}
    (s : Fin m → Γ(M, V)) (s' : Fin m → Γ(M', V)) (h : ∀ i, s' i = u • (φ.hom.app V) (s i)) :
    Scheme.Modules.IsSectionBasisOn f M V s ↔ Scheme.Modules.IsSectionBasisOn f M' V s' := by

  let ψ : Γ(M, V) → Γ(M', V) := fun x => u • (φ.hom.app V) x
  have hψ : Function.Bijective ψ := by
    obtain ⟨w, rfl⟩ := hu
    refine Function.bijective_iff_has_inverse.mpr ⟨fun y => (φ.inv.app V) (((w⁻¹ : (Γ(X, V))ˣ) : Γ(X, V)) • y), ?_, ?_⟩
    · intro x
      change (φ.inv.app V) (((w⁻¹ : (Γ(X, V))ˣ) : Γ(X, V)) • ((w : Γ(X, V)) • (φ.hom.app V) x)) = x
      rw [smul_smul, Units.inv_mul, one_smul, iso_inv_hom_apply]
    · intro y
      change (w : Γ(X, V)) • (φ.hom.app V) ((φ.inv.app V) (((w⁻¹ : (Γ(X, V))ˣ) : Γ(X, V)) • y)) = y
      have : (φ.hom.app V) ((φ.inv.app V) (((w⁻¹ : (Γ(X, V))ˣ) : Γ(X, V)) • y)) =
          ((w⁻¹ : (Γ(X, V))ˣ) : Γ(X, V)) • y := by
        change ((φ.inv.app V) ≫ (φ.hom.app V)) _ = _
        rw [← Scheme.Modules.Hom.comp_app, φ.inv_hom_id, Scheme.Modules.Hom.id_app]
        rfl
      rw [this, smul_smul, Units.mul_inv, one_smul]
  have hcomp : (fun c : Fin m → S =>
      ∑ i, ((f.appLE ⊤ V le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (c i))) • s' i) =
      ψ ∘ (fun c : Fin m → S => ∑ i, ((f.appLE ⊤ V le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (c i))) • s i) := by
    funext c
    simp only [Function.comp_apply, ψ, map_sum, Finset.smul_sum, Scheme.Modules.Hom.app_smul, h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_comm]
  unfold Scheme.Modules.IsSectionBasisOn
  rw [hcomp]
  exact ⟨fun hb => hψ.comp hb, fun hb => (Function.Bijective.of_comp_iff' hψ _).mp hb⟩

end LinSysSol

theorem solution
    {S S' : Type} [CommRing S] [CommRing S'] [Algebra S S'] {N : ℕ}
    {Z Z' : Scheme.{0}} {f : Z ⟶ Spec (CommRingCat.of S)} {f' : Z' ⟶ Spec (CommRingCat.of S')}
    {L : Z.Modules} {L' : Z'.Modules}
    (𝔓 : Scheme.Modules.ProjPresentation L f N) (𝔓' : Scheme.Modules.ProjPresentation L' f' N)
    (e : Z' ⟶ Z) (heι : e ≫ 𝔓.toProj = 𝔓'.toProj ≫ ProjSpace.map S S' N)
    {S'' : Type} [CommRing S''] {A : Scheme.{0}} (f'' : A ⟶ Spec (CommRingCat.of S'')) (g : A ⟶ Z') :
    Scheme.Modules.IsSectionBasisOn f'' ((Scheme.Modules.pullback (g ≫ e)).obj L) ((g ≫ e) ⁻¹ᵁ ⊤)
        (fun i => Scheme.Modules.pullbackLocalSection (g ≫ e) (𝔓.σ i)) ↔
      Scheme.Modules.IsSectionBasisOn f'' ((Scheme.Modules.pullback g).obj L') (g ⁻¹ᵁ ⊤)
        (fun i => Scheme.Modules.pullbackLocalSection g (𝔓'.σ i)) := by
  classical

  obtain ⟨𝔓e, hσe, htoe⟩ :=
    AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_projPresentation_pullback_sigma_eq_toProj_eq e 𝔓
  obtain ⟨𝔓r, hσr, htor⟩ :=
    AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_sigma_eq_toProj_eq_comp_map_of_algebraMap (R := S) 𝔓'
  have hbase : e ≫ f = f' ≫ Spec.map (CommRingCat.ofHom (algebraMap S S')) := by
    rw [← 𝔓.toProj_π, ← Category.assoc, heι, Category.assoc, (ProjSpace.isPullback_map S S' N).w, ← Category.assoc,
      𝔓'.toProj_π]
  have hto : (LinSysSol.castBase hbase 𝔓e).toProj = 𝔓r.toProj := by
    rw [LinSysSol.castBase_toProj, htoe, htor, heι]
  obtain ⟨F⟩ := AlgebraicGeometry.Scheme.Modules.ProjPresentation.nonempty_iso_of_toProj_eq (LinSysSol.castBase hbase 𝔓e) 𝔓r hto
  obtain ⟨𝔓t, htot, hσt⟩ := AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_of_iso (LinSysSol.castBase hbase 𝔓e) F
  obtain ⟨u, hu⟩ := AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_unit_smul_eq_of_toProj_eq 𝔓t 𝔓r (htot.trans hto)
  have hσ' : ∀ i, 𝔓'.σ i = (u : Γ(Z', ⊤)) • (F.hom.app ⊤) (Scheme.Modules.pullbackLocalSection e (𝔓.σ i)) := by
    intro i
    rw [← hσr i, hu i, hσt i, LinSysSol.castBase_σ, hσe i]
    rfl

  let Φ : (Scheme.Modules.pullback (g ≫ e)).obj L ≅ (Scheme.Modules.pullback g).obj L' :=
    ((Scheme.Modules.pullbackComp g e).app L).symm ≪≫ (Scheme.Modules.pullback g).mapIso F
  refine LinSysSol.isSectionBasisOn_iff_of_iso f'' ((g ≫ e) ⁻¹ᵁ ⊤) Φ (g.app ⊤ (u : Γ(Z', ⊤))) ((u.isUnit).map _) _ _ ?_
  intro i
  have h43 := AlgebraicGeometry.Scheme.Modules.pullbackComp_hom_app_pullbackLocalSection g e L ⊤ (𝔓.σ i)
  have h43' : (((Scheme.Modules.pullbackComp g e).app L).inv.app _) (Scheme.Modules.pullbackLocalSection (g ≫ e) (𝔓.σ i)) =
      Scheme.Modules.pullbackLocalSection g (Scheme.Modules.pullbackLocalSection e (𝔓.σ i)) := by
    rw [← h43]
    exact LinSysSol.iso_inv_hom_apply _ _ _
  have hΦ : (Φ.hom.app ((g ≫ e) ⁻¹ᵁ ⊤)) (Scheme.Modules.pullbackLocalSection (g ≫ e) (𝔓.σ i)) =
      (((Scheme.Modules.pullback g).map F.hom).app _) (Scheme.Modules.pullbackLocalSection g (Scheme.Modules.pullbackLocalSection e (𝔓.σ i))) := by
    rw [← h43']
    rfl
  rw [hΦ, hσ' i, Scheme.Modules.pullbackLocalSection_smul, Scheme.Modules.pullbackLocalSection_app]
  rfl

end S_AlgebraicGeometry_Scheme_Modules_isSectionBasisOn_pullback_comp_iff_of_toProj_comp_eq
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_isSectionBasisOn_pullback_comp_iff_of_toProj_comp_eq (solution)
