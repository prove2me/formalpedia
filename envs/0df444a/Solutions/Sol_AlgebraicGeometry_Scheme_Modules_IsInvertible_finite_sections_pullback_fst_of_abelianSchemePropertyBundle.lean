-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.finite_sections_pullback_fst_of_abelianSchemePropertyBundle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/5d08096b-44da-53dd-b447-462e9a974296

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_ofModules_of_locallyTrivial
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_baseChange_of_field
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_finite_sections_pullback_fst_of_abelianSchemePropertyBundle
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"
theorem solution
    (k : Type) [Field k] {A : Scheme} (f : A ⟶ Spec (CommRingCat.of k)) (hA : AbelianSchemePropertyBundle k f)
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M) (k' : Type) [Field k'] (sk : k →+* k') :
    letI : Algebra k' Γ(Limits.pullback f (Spec.map (CommRingCat.ofHom sk)), ⊤) :=
      ((Scheme.ΓSpecIso (.of k')).inv ≫
        (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom sk))).appLE ⊤ ⊤ le_top).hom.toAlgebra
    letI : Module k' Γ((Scheme.Modules.pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk)))).obj M, ⊤) :=
      Module.compHom _ (algebraMap k' Γ(Limits.pullback f (Spec.map (CommRingCat.ofHom sk)), ⊤))
    Module.Finite k' Γ((Scheme.Modules.pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk)))).obj M, ⊤) := by

  let g := Spec.map (CommRingCat.ofHom sk)
  let X := Limits.pullback f g
  let π : X ⟶ Spec (CommRingCat.of k') := Limits.pullback.snd f g
  let p₁ : X ⟶ A := Limits.pullback.fst f g
  let M' : X.Modules := (Scheme.Modules.pullback p₁).obj M
  have hA' : AbelianSchemePropertyBundle k' π := hA.baseChange_of_field g
  haveI : IsProper π := hA'.proper
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace π
  have hM' : Scheme.Modules.IsInvertible M' := hM.pullback p₁

  let 𝒰 := X.affineCover.finiteSubcover
  let e := Fintype.equivFin 𝒰.I₀
  let K : X.OrderedAffineCover :=
    { ι := Fin (Fintype.card 𝒰.I₀)
      U := fun i => (𝒰.f (e.symm i)).opensRange
      isAffineOpen := fun i => isAffineOpen_opensRange _
      iSup_eq_top := by
        rw [← 𝒰.iSup_opensRange]
        exact e.symm.surjective.iSup_comp (fun j => (𝒰.f j).opensRange) }

  let F := OModulePresheaf.ofModules π M'
  have hfin : F.CechFinite K :=
    OModulePresheaf.cechFinite_ofModules_of_locallyTrivial π M' hM'.exists_trivialization K
  haveI hH0 : Module.Finite k' (F.H0 K) := hfin.1

  letI instK : ∀ U : X.Opens, Module k' Γ(M', U) := fun U => Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M' U
  let ρ : Γ(M', ⊤) →ₗ[k'] F.cochain K 0 :=
    LinearMap.pi fun s => Scheme.TwoAffineOpenCover.restrictSections π M' (le_top : K.inter s ≤ ⊤)
  have hρ : ∀ m, ρ m ∈ F.H0 K := by
    intro m
    rw [LinearMap.mem_ker]
    funext s
    rw [OModulePresheaf.d_apply]
    show ∑ j : Fin 2, ((-1 : ℤ) ^ (j : ℕ)) • F.res (K.inter_le_inter_face s j) (F.res le_top m) = 0
    simp only [OModulePresheaf.res_res, Fin.sum_univ_two, Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one,
      neg_smul, add_neg_cancel]
  let φ : Γ(M', ⊤) →ₗ[k'] F.H0 K := LinearMap.codRestrict (F.H0 K) ρ hρ
  have hφ : Function.Injective φ := by
    intro m₁ m₂ h
    have h' : ∀ s : K.Idx 0, M'.presheaf.map (homOfLE (le_top : K.inter s ≤ ⊤)).op m₁ =
        M'.presheaf.map (homOfLE (le_top : K.inter s ≤ ⊤)).op m₂ := by
      intro s
      have := congrArg (fun c : F.H0 K => (c : F.cochain K 0) s) h
      exact this

    have hcov : (⊤ : X.Opens) ≤ ⨆ s : K.Idx 0, K.inter s := by
      rw [← K.iSup_eq_top]
      refine iSup_le fun i => ?_
      refine le_trans ?_ (le_iSup (fun s : K.Idx 0 => K.inter s) ⟨fun _ => i, fun a b hab => absurd hab (by omega)⟩)
      exact le_iInf fun _ => le_rfl
    exact TopCat.Sheaf.eq_of_locally_eq' (⟨M'.presheaf, M'.isSheaf⟩ : TopCat.Sheaf Ab X.carrier)
      (fun s : K.Idx 0 => K.inter s) ⊤ (fun s => homOfLE le_top) hcov m₁ m₂ h'
  exact Module.Finite.of_injective φ hφ

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_finite_sections_pullback_fst_of_abelianSchemePropertyBundle
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_finite_sections_pullback_fst_of_abelianSchemePropertyBundle (solution)
